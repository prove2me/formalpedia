-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:19.158145+00:00
-- url     : https://prove2.me/submissions/8ab840d3-7f87-42ad-8133-1b6476c9d810

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : A → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) :=
  hbf.smul_real hU hs hC hD hf hg hbg

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetWordDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every ordered coordinate jet is a derivative of a component of the
actual second jet, with precisely the excess derivative count. -/
noncomputable section

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma exists_lowWord (w : List (Fin 2)) (hw : w.length ≤ 2) :
    ∃ i : Fin 7, lowWord i = w := by
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil =>
      fin_cases a
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | cons b w =>
      have he : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      fin_cases a <;> fin_cases b
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

lemma split_lowWord (w : List (Fin 2)) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, w = v ++ lowWord i ∧ v.length = w.length - 2 := by
  obtain ⟨i, hi⟩ := exists_lowWord (w.drop (w.length - 2)) (by
    rw [List.length_drop]
    omega)
  refine ⟨w.take (w.length - 2), i, ?_, ?_⟩
  · rw [hi, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

lemma iteratedDirectional_append {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : List A) (f : A → E) :
    iteratedDirectional (v ++ w) f = iteratedDirectional v (iteratedDirectional w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append, iteratedDirectional, ih]

/-- The scale loss of an ordered jet factor is its derivative order minus two. -/
lemma jet_as_lowJet_derivative (w : List (Fin 2)) (a : Fin 4) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, v.length = w.length - 2 ∧
      ∀ (G : Base → Space), jet G w a =
        iteratedDirectional (v.map coordinateVector) (fun p => lowJet G p (Sum.inr (i, a))) := by
  obtain ⟨v, i, hw, hv⟩ := split_lowWord w
  refine ⟨v, i, hv, ?_⟩
  intro G
  change iteratedDirectional (w.map coordinateVector) (fun p => G p a) = _
  rw [hw, List.map_append, iteratedDirectional_append]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariations
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_affine {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (p : Base) :
    lowJet (fun q => G q + t • H q) p = lowJet G p + t • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [lowJet, variationLowJet]
  | inr i =>
    change jet (fun q => G q + t • H q) (lowWord i.1) i.2 p = _
    rw [jet_add (H := fun q => t • H q) hG (ContDiff.const_smul t hH), jet_smul hH]
    rfl

lemma lowJet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lowJet (fun q => G q + s • H q) p) (variationLowJet H p) t := by
  have he : (fun s : ℝ => lowJet (fun q => G q + s • H q) p) =
      (fun s : ℝ => lowJet G p + s • variationLowJet H p) :=
    funext (fun s => lowJet_affine hG hH s p)
  rw [he]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (variationLowJet H p)).const_add (lowJet G p)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalIsometryBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric coordinate transport on the open domains used by the local
polynomial estimates. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weightedBound_comp_isometry_on {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) {U : Set B} (hU : IsOpen U) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound U s m C f) :
    WeightedBound (e ⁻¹' U) s m C (f ∘ e) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j (hU.preimage e.continuous) hx]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  have hh := hb j hj (e x) hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hh
  exact hh

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r5d62f7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedLowCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

/-- The same constant controls every angular slice over the unit period. -/
theorem compact_low_coefficient {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hcompact : IsCompact (K ×ˢ Set.Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn hcompact hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first variation of an actual higher-jet polynomial, including the
variation of its smooth second-jet coefficients. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

theorem variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : Expression} (he : e.SmoothCoeffs O) (z : Base × ℝ)
    (hQ : lowJet G z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (fun p => G p + s • H p) z) (e.variation G H z) 0 := by
  induction e with
  | coeff c =>
    have hmem : (lowJet G z.1, z.2) ∈ O ×ˢ Set.univ := ⟨hQ, Set.mem_univ z.2⟩
    have hc : DifferentiableAt ℝ c (lowJet G z.1, z.2) :=
      (he.contDiffAt ((hO.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hj := (lowJet_affine_hasDerivAt hG hH z.1 0).prodMk (hasDerivAt_const 0 z.2)
    have hd := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hj (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [Function.comp_def, zero_smul, add_zero, eval, variation] using hd
  | atom w a e ih =>
    have hj : HasDerivAt (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1)
        (jet H w a z.1) 0 := by
      have hpath : (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1) =
          (fun s : ℝ => jet G w a z.1 + s * jet H w a z.1) := by
        funext s
        rw [jet_add (H := fun p => s • H p) hG (ContDiff.const_smul s hH), jet_smul hH]
      rw [hpath]
      simpa only [one_mul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (jet H w a z.1)).const_add (jet G w a z.1)
    have hzero : (fun p => G p + (0 : ℝ) • H p) = G := by funext p; simp
    simpa only [eval, variation, hzero, Pi.mul_apply] using hj.fun_mul (ih he)
  | add e f ihe ihf =>
    exact (ihe he.1).add (ihf he.2)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-variation estimate for every finite higher-jet polynomial.
Its scale exponent is fixed by the polynomial, independently of output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_plain_jet {U : Set Base} (hU : IsOpen U) {H : Base → Space}
    (hH : ContDiff ℝ ∞ H) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + w.length) C H) :
    WeightedBound U s m (C / s ^ w.length) (jet H w a) := by
  have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
  have hcw : WeightedBound U s (m + (w.map coordinateVector).length) C (fun p => H p a) := by
    simpa only [List.length_map] using hc
  change WeightedBound U s m (C / s ^ w.length)
    (iteratedDirectional (w.map coordinateVector) (fun x => H x a))
  simpa only [List.length_map] using hcw.iteratedDirectional hU hs hC
    (contDiff_pi.mp hH a).contDiffOn (w.map coordinateVector)
    (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le i) m

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_eval (e : Expression) (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (ofExpression e).eval G z = e.eval (G 0) z := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, eval, Expression.eval, ih]
  | add _ _ ihe ihf => simp only [ofExpression, eval, Expression.eval, ihe, ihf]

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

theorem eval_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth (hG 0)).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)
  | atom i w a e ih =>
    exact (((jet_smooth (hG i) w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma parameter_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedMixedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mixed-variation bounds with the sharp excess-jet scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

/-- Unit weighted bounds on the direction maps cost their full jet orders;
the base map costs only the order beyond its controlled second jet. -/
theorem compact_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / s ^ e.loss) (fun p => e.eval G (p, t)) := by
  induction e with
  | coeff c =>
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient hU hO hK hKO he m B hB
    refine ⟨D, hD, ?_⟩
    intro G s hs _ hG hGK hb _ t ht
    simpa only [loss, pow_zero, div_one, eval] using
      hd (lowJet (G 0)) s hs (lowJet_smooth (hG 0)).contDiffOn hGK
        (hb.mono_order (by omega)) t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have htail := hd G s hs hs1 hG hGK
      (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hj : WeightedBound U s m
        (B / s ^ (if i = 0 then w.length - 2 else w.length)) (jet (G i) w a) := by
      by_cases hi : i = 0
      · subst i
        simp only [↓reduceIte]
        exact weighted_actual_jet hU (hG 0) hs (zero_le_one.trans hB) m w a
          (hb.mono_order (by simp only [order]; omega))
      · let j : Fin 3 := i.pred hi
        have hij : i = j.succ := (Fin.succ_pred i hi).symm
        rw [hij]
        simp only [Fin.succ_ne_zero, ↓reduceIte]
        exact (weighted_plain_jet hU (hG j.succ) hs zero_le_one m w a
          ((hv j).mono_order (by simp only [order]; omega))).mono_const
            (div_le_div_of_nonneg_right hB (pow_nonneg hs.le _))
    have hp := hj.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth (hG i) w a).contDiffOn (parameter_smooth hG hQ (e := e) he t) htail
    convert hp using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hc' := hc G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hd'' : WeightedBound U s m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hs.le
      (parameter_smooth hG hQ (e := e) he.1 t) (parameter_smooth hG hQ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetCalculus
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_expansion (H : Base → Space) (p : Base) :
    variationLowJet H p = ∑ i : Fin 7 × Fin 4,
      jet H (lowWord i.1) i.2 p • lowBasis (.inr i) := by
  funext k
  cases k with
  | inl k => simp [variationLowJet, lowBasis]
  | inr k => simp [variationLowJet, lowBasis, Pi.single_apply]

lemma coefficient_variation_sum (c : LowJet × ℝ → ℝ) (G H : Base → Space) (z : Base × ℝ) :
    fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0) =
      ∑ i : Fin 7 × Fin 4, jet H (lowWord i.1) i.2 z.1 *
        fderiv ℝ c (lowJet G z.1, z.2) (lowBasis (.inr i), 0) := by
  let L : LowJet →L[ℝ] ℝ :=
    (fderiv ℝ c (lowJet G z.1, z.2)).comp (ContinuousLinearMap.inl ℝ LowJet ℝ)
  change L (variationLowJet H z.1) = _
  rw [variationLowJet_expansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

namespace MixedExpression

lemma sumList_eval {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma differentiate_coeff_eval (c : LowJet × ℝ → ℝ) (j : Fin 3)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    ((coeff c).differentiate j).eval G z =
      fderiv ℝ c (lowJet (G 0) z.1, z.2) (variationLowJet (G j.succ) z.1, 0) := by
  rw [coefficient_variation_sum]
  simp only [differentiate, sumList_eval, eval, coefficientDerivative]
  exact Finset.sum_map_toList _ _

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual differentiation of mixed jet polynomials in the base-map slot. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

lemma jet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => jet (fun q => G q + s • H q) w a p)
      (jet H w a p) t := by
  have hpath : (fun s : ℝ => jet (fun q => G q + s • H q) w a p) =
      (fun s : ℝ => jet G w a p + s * jet H w a p) := by
    funext s
    rw [jet_add (H := fun q => s • H q) hG (ContDiff.const_smul s hH), jet_smul hH]
  rw [hpath]
  simpa only [one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (jet H w a p)).const_add (jet G w a p)

namespace MixedExpression

lemma varyBase_zero (G : Fin 4 → Base → Space) (H : Base → Space) : varyBase G H 0 = G := by
  funext i p
  by_cases hi : i = 0 <;> simp [varyBase, hi]

lemma varyBase_base (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ) :
    varyBase G H s 0 = fun p => G 0 p + s • H p := by
  funext p
  simp only [varyBase, ↓reduceIte]

lemma varyBase_other (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ)
    {i : Fin 4} (hi : i ≠ 0) : varyBase G H s i = G i := by
  funext p
  simp only [varyBase, hi, ↓reduceIte]

/-- The syntactic derivative evaluates to the actual derivative, while the
three direction slots remain fixed. -/
theorem differentiate_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (z : Base × ℝ)
    (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval G z) 0 := by
  induction e with
  | coeff c =>
    have hd := Expression.variation_hasDerivAt hO (hG 0) (hG j.succ)
      (e := .coeff c) he z hQ
    simpa only [eval, varyBase_base, Expression.eval, Expression.variation,
      differentiate_coeff_eval] using hd
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      have hj := jet_affine_hasDerivAt (hG 0) (hG j.succ) w a z.1 0
      have hd := hj.fun_mul (ih he)
      simpa only [eval, varyBase_base, varyBase_zero, differentiate, ↓reduceIte,
        Pi.mul_apply, zero_smul, add_zero] using hd
    · have hj := (hasDerivAt_const (0 : ℝ) (jet (G i) w a z.1)).fun_mul (ih he)
      simpa only [eval, varyBase_other G (G j.succ) _ hi, varyBase_zero,
        differentiate, hi, ↓reduceIte, zero_mul, zero_add, Pi.mul_apply] using hj
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetHomogeneity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneity in each variation slot, including the zero polynomial. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma scaleSlot_base (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) :
    scaleSlot G j c 0 = G 0 := by
  funext p
  simp only [scaleSlot, Ne.symm (Fin.succ_ne_zero j), ↓reduceIte]

lemma scaleSlot_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (j : Fin 3) (c : ℝ) : ∀ i, ContDiff ℝ ∞ (scaleSlot G j c i) := by
  intro i
  change ContDiff ℝ ∞ (fun p => if i = j.succ then c • G i p else G i p)
  by_cases hi : i = j.succ
  · simpa only [scaleSlot, hi, ↓reduceIte] using ContDiff.const_smul c (hG j.succ)
  · simpa only [scaleSlot, hi, ↓reduceIte] using hG i

theorem DegreeIn.eval_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : ℝ) (z : Base × ℝ) :
    e.eval (scaleSlot G j c) z = c ^ n * e.eval G z := by
  induction h with
  | coeff d => simp only [eval, scaleSlot_base, pow_zero, one_mul]
  | zero n => simp only [eval, mul_zero]
  | other i w a hi h ih =>
    have he : scaleSlot G j c i = G i := by
      funext p
      simp only [scaleSlot, hi, ↓reduceIte]
    simp only [eval, he, ih]
    ring
  | same w a h ih =>
    have he : scaleSlot G j c j.succ = fun p => c • G j.succ p := by
      funext p
      simp only [scaleSlot, ↓reduceIte]
    simp only [eval, he, jet_smul (hG j.succ), ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [eval, ihe, ihf, mul_add]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

lemma first_variation_eval {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    (e.variations 0).eval G z = e.variation (G 0) (G 1) z := by
  have ha := differentiate_hasDerivAt hO hG (smoothCoeffs_ofExpression he) 0 z hQ
  have hb := variation_hasDerivAt hO (hG 0) (hG 1) he z hQ
  have ha' : HasDerivAt (fun s : ℝ => e.eval (fun p => G 0 p + s • G 1 p) z)
      ((e.variations 0).eval G z) 0 := by
    change HasDerivAt _ (((ofExpression e).differentiate 0).eval G z) 0
    simpa only [ofExpression_eval, varyBase_base, Fin.succ_zero_eq_one] using ha
  exact ha'.unique hb

/-- The constant can depend on the requested output order; the exponent and
finite input loss do not. All three direction maps have unit weighted norm. -/
theorem compact_three_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / s ^ (e.loss + 6))
          (fun p => (e.variations i).eval G (p, t)) := by
  classical
  have hex := fun i : Fin 3 => compact_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m B hB
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G s hs hs1 hG hGK hGb hHb t ht i
  have hi := hb i G s hs hs1 hG hGK
    (hGb.mono_order (Nat.add_le_add_left (e.variations_order i) m))
    (fun j => (hHb j).mono_order (Nat.add_le_add_left (e.variations_order i) m)) t ht
  apply hi.mono_const
  calc
    D i / s ^ (e.variations i).loss ≤ D i / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_left (hD i) (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (e.variations_loss i))
    _ ≤ (∑ j, D j) / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_right (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))
        (pow_nonneg hs.le _)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multilinear scaling of the three actual polynomial variations. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace MixedExpression

lemma rescale_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (c : Fin 3 → ℝ) : ∀ i, ContDiff ℝ ∞ (rescale G c i) := by
  intro i
  fin_cases i
  · exact hG 0
  · exact ContDiff.const_smul (c 0) (hG 1)
  · exact ContDiff.const_smul (c 1) (hG 2)
  · exact ContDiff.const_smul (c 2) (hG 3)

lemma rescale_eq (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) :
    rescale G c = scaleSlot (scaleSlot (scaleSlot G 0 (c 0)) 1 (c 1)) 2 (c 2) := by
  funext i p
  fin_cases i <;> simp [rescale, scaleSlot]

lemma eval_rescale {e : MixedExpression} {n : Fin 3 → ℕ}
    (he : ∀ j, DegreeIn j e (n j)) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) :
    e.eval (rescale G c) z =
      (c 0 ^ n 0 * c 1 ^ n 1 * c 2 ^ n 2) * e.eval G z := by
  rw [rescale_eq, (he 2).eval_scaleSlot
    (scaleSlot_smooth (scaleSlot_smooth hG 0 (c 0)) 1 (c 1)),
    (he 1).eval_scaleSlot (scaleSlot_smooth hG 0 (c 0)), (he 0).eval_scaleSlot hG]
  ring

end MixedExpression
namespace Expression

lemma variations_rescale (e : Expression) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) (i : Fin 3) :
    (e.variations i).eval (rescale G c) z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) *
        (e.variations i).eval G z := by
  have h := eval_rescale (fun j => e.variations_degree i j) hG c z
  fin_cases i <;> simpa using h

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAffineFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint smoothness in position and a variation parameter for actual
higher-jet polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma jet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) := by
  have he : (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) =
      fun z => jet G w a z.1 + z.2 * jet H w a z.1 := by
    funext z
    rw [jet_add hG (hH.const_smul z.2), jet_smul hH]
  rw [he]
  exact ((jet_smooth hG w a).comp contDiff_fst).add
    (contDiff_snd.mul ((jet_smooth hH w a).comp contDiff_fst))

lemma lowJet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) := by
  have he : (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) =
      fun z => lowJet G z.1 + z.2 • variationLowJet H z.1 := by
    funext z
    exact lowJet_affine hG hH z.2 z.1
  rw [he]
  exact ((lowJet_smooth hG).comp contDiff_fst).add
    (contDiff_snd.smul ((variationLowJet_smooth hH).comp contDiff_fst))

namespace MixedExpression

lemma jet_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (varyBase G H z.2 i) w a z.1) := by
  by_cases hi : i = 0
  · subst i
    simpa only [varyBase_base] using jet_affine_joint_smooth (hG 0) hH w a
  · simpa only [varyBase_other G H _ hi, Function.comp_def] using (jet_smooth (hG i) w a).comp contDiff_fst

/-- Global coefficient smoothness is obtained on the application compact set
by `Expression.exists_global_extension`. -/
theorem eval_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => e.eval (varyBase G H z.2) (z.1, θ)) := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs, Set.univ_prod_univ] using he)
    have hh := hc.comp ((lowJet_affine_joint_smooth (hG 0) hH).prodMk (contDiff_const (c := θ)))
    simpa only [eval, varyBase_base, Function.comp_def] using hh
  | atom i w a e ih =>
    exact (jet_varyBase_joint_smooth hG hH i w a).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAffineDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial variations at every point of an affine path, rather
than only at the parameter origin. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma varyBase_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H) (t : ℝ) :
    ∀ i, ContDiff ℝ ∞ (varyBase G H t i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [varyBase_base]
    exact (hG 0).add (hH.const_smul t)
  · rw [varyBase_other G H t hi]
    exact hG i

lemma varyBase_add (G : Fin 4 → Base → Space) (H : Base → Space) (t s : ℝ) :
    varyBase (varyBase G H t) H s = varyBase G H (t + s) := by
  funext i p
  by_cases hi : i = 0
  · simp only [varyBase, hi, ↓reduceIte, add_smul]
    abel
  · simp only [varyBase, hi, ↓reduceIte]

theorem differentiate_hasDerivAt_at {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (t : ℝ) (z : Base × ℝ)
    (hQ : lowJet (varyBase G (G j.succ) t 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) t := by
  have hd := differentiate_hasDerivAt hO (varyBase_smooth hG (hG j.succ) t) he j z hQ
  rw [varyBase_other G (G j.succ) t (Fin.succ_ne_zero j)] at hd
  have hd' : HasDerivAt
      (fun s : ℝ => e.eval (varyBase (varyBase G (G j.succ) t) (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) (t - t) := by
    simpa only [sub_self] using hd
  have hs := hd'.comp_sub_const t t
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  rw [varyBase_add]
  congr 2
  ring

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CubicTaylorRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order integral remainder needed after the finite quadratic
mean correction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma quadraticTaylor_value {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    taylorWithinEval f 2 (uIcc (0 : ℝ) 1) 0 1 =
      f 0 + deriv f 0 + (1 / 2 : ℝ) • iteratedDeriv 2 f 0 := by
  have hi (k : ℕ) : iteratedDerivWithin k f (uIcc (0 : ℝ) 1) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)).contDiffAt) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [show 2 = 1 + 1 from rfl, taylorWithinEval_succ, taylorWithinEval_succ,
    taylor_within_zero_eval, hi 1, hi 2]
  norm_num

lemma cubicTaylor_remainder {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    f 1 - f 0 - deriv f 0 - (1 / 2 : ℝ) • iteratedDeriv 2 f 0 =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • iteratedDeriv 3 f t := by
  have ht := taylor_integral_remainder (f := f) (n := 2) (x₀ := 0) (x := 1)
    (hf.of_le (by simp : ((2 + 1 : ℕ) : ℕ∞ω) ≤ ∞)).contDiffOn
  rw [quadraticTaylor_value hf] at ht
  have hi : (∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
      iteratedDerivWithin 3 f (uIcc (0 : ℝ) 1) t) =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • iteratedDeriv 3 f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (3 : ℕ∞ω) ≤ ∞)).contDiffAt) ht]
    norm_num
  rw [hi] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  abel

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ParameterIntegralDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every parameter derivative commutes with a compact interval integral.
This supplies the weighted bounds for periodic means and primitives. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma partialIterated_succ {F : P × ℝ → E} (n : ℕ)
    (h : ContDiff ℝ ∞ (partialIterated n F)) :
    partialIterated (n + 1) F = fun z =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm
        (partialDerivative (partialIterated n F) z) := by
  funext z
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm
    (fderiv ℝ (fun p => partialIterated n F (p, z.2)) z.1) = _
  rw [(partial_hasFDerivAt h z.1 z.2).fderiv]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma contDiff_partialIterated {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (partialIterated n F) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ P E).symm.contDiff.comp hF
  | succ n ih =>
    rw [partialIterated_succ n ih]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm.contDiff.comp
      (contDiff_partialDerivative ih)

/-- The actual all-order derivative formula, with no separate derivative
interchange hypothesis. -/
theorem iteratedFDeriv_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (n : ℕ) (p : P) :
    iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t)) p =
      ∫ t in a..b, partialIterated n F (p, t) := by
  induction n generalizing p with
  | zero =>
    let L : E →L[ℝ] (P [×0]→L[ℝ] E) :=
      (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change L (∫ t in a..b, F (p, t)) = ∫ t in a..b, L (F (p, t))
    exact (L.intervalIntegral_comp_comm
      ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)).symm
  | succ n ih =>
    let L : (P →L[ℝ] P [×n]→L[ℝ] E) →L[ℝ] (P [×(n + 1)]→L[ℝ] E) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hFn := contDiff_partialIterated hF n
    have he : iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t)) =
        fun q => ∫ t in a..b, partialIterated n F (q, t) := funext ih
    change L (fderiv ℝ (iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t))) p) = _
    rw [he, (hasFDerivAt_integral hFn a b p).fderiv]
    have hInt : IntervalIntegrable (fun t => partialDerivative (partialIterated n F) (p, t))
        volume a b := ((contDiff_partialDerivative hFn).continuous.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    rw [← L.intervalIntegral_comp_comm hInt]
    apply intervalIntegral.integral_congr
    intro t _
    exact (congrFun (partialIterated_succ n hFn) (p, t)).symm

end ClosedSurfaceR4.SmoothParameterIntegral
namespace ClosedSurfaceR4.WeightedEstimates
open SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Parameter integration preserves every weighted derivative bound, with
only the length of the integration interval as an operator bound. -/
theorem weighted_parameter_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (m : ℕ) (a b : ℝ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.uIcc a b,
      s ^ j * ‖partialIterated j F (p, t)‖ ≤ C) :
    WeightedBound U s m (C * |b - a|) (fun p => ∫ t in a..b, F (p, t)) := by
  have hI := contDiff_integral hF a b
  intro j hj p hp
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    ((hI.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp,
    iteratedFDeriv_integral hF]
  have hn : ‖∫ t in a..b, partialIterated j F (p, t)‖ ≤ C / s ^ j * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    exact (le_div_iff₀ (pow_pos hs j)).mpr (by
      simpa only [mul_comm] using hb j hj p hp t (Set.uIoc_subset_uIcc ht))
  calc
    s ^ j * ‖∫ t in a..b, partialIterated j F (p, t)‖ ≤
        s ^ j * (C / s ^ j * |b - a|) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hs.le j)
    _ = C * |b - a| := by field_simp [hs.ne']

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ParameterTaylorRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic Taylor remainders retain all weighted spatial derivative bounds
under integration in the variation parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.ParameterTaylor
open SmoothPeriodicCalculus SmoothParameterIntegral WeightedEstimates

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parameterJet_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    ContDiff ℝ ∞ (parameterJet j F) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact contDiff_angleDerivative ih

lemma parameterJet_apply {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (j : ℕ) (p : A) (t : ℝ) :
    parameterJet j F (p, t) = iteratedDeriv j (fun r => F (p, r)) t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    change angleDerivative (parameterJet j F) (p, t) = _
    rw [← (angle_hasDerivAt (parameterJet_smooth hF j) p t).deriv]
    have he : (fun r => parameterJet j F (p, r)) = iteratedDeriv j (fun r => F (p, r)) := funext ih
    rw [he, ← iteratedDeriv_succ]

lemma cubicRemainder_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (cubicRemainder F) :=
  (((hF.comp (contDiff_id.prodMk contDiff_const)).sub
    (hF.comp (contDiff_id.prodMk contDiff_const))).sub
    ((parameterJet_smooth hF 1).comp (contDiff_id.prodMk contDiff_const))).sub
    (((parameterJet_smooth hF 2).comp (contDiff_id.prodMk contDiff_const)).const_smul (1 / 2 : ℝ))

variable [CompleteSpace E]

lemma cubicRemainder_eq_integral {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : A) :
    cubicRemainder F p = ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • parameterJet 3 F (p, t) := by
  have hslice : ContDiff ℝ ∞ (fun t => F (p, t)) := hF.comp (contDiff_const.prodMk contDiff_id)
  simp only [cubicRemainder, parameterJet_apply hF, iteratedDeriv_one]
  exact cubicTaylor_remainder hslice

variable [FiniteDimensional ℝ A]

/-- A uniform weighted estimate for the third variation gives the same
weighted estimate for the actual nonlinear Taylor remainder. -/
theorem weighted_cubicRemainder {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set A} (hU : IsOpen U) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (parameterJet 3 F) (p, t)‖ ≤ M) :
    WeightedBound U s m (M / 2) (cubicRemainder F) := by
  let R : A × ℝ → E := fun z => ((1 - z.2) ^ 2 / 2) • parameterJet 3 F z
  have hJ := parameterJet_smooth hF 3
  have hR : ContDiff ℝ ∞ R :=
    (((contDiff_const.sub contDiff_snd).pow 2).div_const 2).smul hJ
  have hi := weighted_parameter_integral (C := M / 2) hR hU hs m 0 1
  have hbound : WeightedBound U s m ((M / 2) * |1 - 0|) (fun p => ∫ t in (0 : ℝ)..1, R (p, t)) := by
    apply hi
    intro j hj p hp t ht
    have htp : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hpart : partialIterated j R (p, t) =
        ((1 - t) ^ 2 / 2) • partialIterated j (parameterJet 3 F) (p, t) := by
      change iteratedFDeriv ℝ j (fun q => ((1 - t) ^ 2 / 2) • parameterJet 3 F (q, t)) p = _
      exact iteratedFDeriv_const_smul_apply'
        (((hJ.comp (contDiff_id.prodMk contDiff_const)).of_le
          (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)).contDiffAt)
    rw [hpart, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 - t) ^ 2 / 2)]
    have hw : (1 - t) ^ 2 / 2 ≤ (1 / 2 : ℝ) := by nlinarith [htp.1, htp.2]
    calc
      _ = ((1 - t) ^ 2 / 2) * (s ^ j * ‖partialIterated j (parameterJet 3 F) (p, t)‖) := by ring
      _ ≤ ((1 - t) ^ 2 / 2) * M := mul_le_mul_of_nonneg_left (hb j hj p hp t htp) (by positivity)
      _ ≤ (1 / 2 : ℝ) * M := mul_le_mul_of_nonneg_right hw hM
      _ = M / 2 := by ring
  have he : (fun p => ∫ t in (0 : ℝ)..1, R (p, t)) = cubicRemainder F := by
    funext p
    exact (cubicRemainder_eq_integral hF p).symm
  simpa only [he, sub_zero, abs_one, mul_one] using hbound

end ClosedSurfaceR4.ParameterTaylor

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDiagonalVariations
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual parameter derivatives of a polynomial along a
map variation are its mixed variations with all directions equal. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ParameterTaylor SmoothPeriodicCalculus

lemma diagonalFamily_smooth {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ∀ i, ContDiff ℝ ∞ (diagonalFamily G H i) := by
  intro i
  refine Fin.cases hG (fun _ => hH) i

lemma diagonalFamily_succ (G H : Base → Space) (j : Fin 3) : diagonalFamily G H j.succ = H := rfl

lemma diagonal_angleDerivative {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (j : Fin 3) (θ : ℝ) (z : Base × ℝ) :
    angleDerivative (fun x : Base × ℝ => e.eval (varyBase (diagonalFamily G H) H x.2) (x.1, θ)) z =
      (e.differentiate j).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  have hs := eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH he θ
  have hd := differentiate_hasDerivAt_at isOpen_univ (diagonalFamily_smooth hG hH) he j z.2
    (z.1, θ) (Set.mem_univ _)
  simp only [diagonalFamily_succ] at hd
  exact (angle_hasDerivAt hs z.1 z.2).unique hd

namespace Expression

lemma affinePolynomial_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.affinePolynomial G H θ) :=
  eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH (smoothCoeffs_ofExpression he) θ

lemma affinePolynomial_first {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 1 (e.affinePolynomial G H θ) =
      fun z => (e.variations 0).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  funext z
  exact diagonal_angleDerivative hG hH (smoothCoeffs_ofExpression he) 0 θ z

lemma affinePolynomial_second {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 2 (e.affinePolynomial G H θ) =
      fun z => (e.variations 1).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  change angleDerivative (parameterJet 1 (e.affinePolynomial G H θ)) = _
  rw [affinePolynomial_first he hG hH]
  funext z
  exact diagonal_angleDerivative hG hH (e.variations_smoothCoeffs isOpen_univ he 0) 1 θ z

lemma affinePolynomial_third {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 3 (e.affinePolynomial G H θ) =
      fun z => (e.variations 2).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  change angleDerivative (parameterJet 2 (e.affinePolynomial G H θ)) = _
  rw [affinePolynomial_second he hG hH]
  funext z
  exact diagonal_angleDerivative hG hH (e.variations_smoothCoeffs isOpen_univ he 1) 2 θ z

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTaylorRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted cubic estimate for the actual higher-jet polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression ParameterTaylor SmoothParameterIntegral WeightedEstimates

lemma affinePolynomial_apply (e : Expression) (G H : Base → Space) (θ : ℝ) (z : Base × ℝ) :
    e.affinePolynomial G H θ z = e.eval (fun p => G p + z.2 • H p) (z.1, θ) := by
  rw [affinePolynomial, ofExpression_eval, varyBase_base]
  rfl

lemma cubicRemainder_affine {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    cubicRemainder (e.affinePolynomial G H θ) = e.taylorRemainder G H θ := by
  funext p
  unfold cubicRemainder taylorRemainder
  rw [affinePolynomial_first he hG hH, affinePolynomial_second he hG hH]
  simp only [affinePolynomial_apply, one_smul, zero_smul, add_zero, varyBase_zero]
  rw [e.first_variation_eval isOpen_univ he (diagonalFamily_smooth hG hH) (p, θ) (Set.mem_univ _)]
  rfl

theorem weighted_taylorRemainder {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ)
    {U : Set Base} (hU : IsOpen U) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j
        (fun z : Base × ℝ => (e.variations 2).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ))
        (p, t)‖ ≤ M) :
    WeightedBound U s m (M / 2) (e.taylorRemainder G H θ) := by
  rw [← cubicRemainder_affine he hG hH θ]
  apply weighted_cubicRemainder (affinePolynomial_smooth he hG hH θ) hU hs hM m
  simpa only [affinePolynomial_third he hG hH] using hb

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialValueBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberSpace
local instance polynomialValueDualAdd_r5d62f7_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialValueDualSmul_r5d62f7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberNormed
local instance polynomialValueSectionNormed_r5d62f7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialValueSectionSpace_r5d62f7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_outer_cutoff (i : A.centers)
    {U : Set JetPolynomial.Base} (hU : IsOpen U)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ U) :
    ∃ (K : Compacts JetPolynomial.Base) (χ : SupportedField (F := ℝ) K),
      tsupport (χ : JetPolynomial.Base → ℝ) ⊆ U ∧
      ∀ p ∈ tsupport (A.outer i), χ (chart (i : M) p) = 1 := by
  let S : Set JetPolynomial.Base := (chart (i : M)) '' tsupport (A.outer i)
  have hS : IsCompact S := (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.outer_support i))
  obtain ⟨V,hV,hSV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hS hU houter
  obtain ⟨χ,hχ,_,hχs,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hS.isClosed hSV
  let K : Compacts JetPolynomial.Base := ⟨closure V,hVc⟩
  let χ' : SupportedField (F := ℝ) K := ContDiffMapSupportedIn.of_support_subset hχ
    (by rw [hχs]; exact subset_closure)
  refine ⟨K,χ',?_,?_⟩
  · change closure (Function.support χ) ⊆ U
    rw [hχs]
    exact hVU
  · intro p hp
    exact (hχone (chart (i : M) p)).mp ⟨p,hp,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberSpace
local instance tensorLocalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberSpace
local instance tensorLocalDualSmul_r5d62f7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberNormed
local instance tensorLocalSectionNormed_r5d62f7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorLocalSectionSpace_r5d62f7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Compact coordinate bounds on the outer supports suffice for global restoration. -/
theorem tensorPlaneRestore_bound_on_outer
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor),
      (∀ i, ContDiff ℝ ∞ (f i)) → ∀ (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      (∀ i, WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' U i) s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  classical
  choose K χ hχU hχone using fun i => A.polynomial_outer_cutoff i (hU i) (houter i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let N : A.centers → ℝ := fun i => supportedWeightedSeminorm (K i) 1 m (χ i)
  have hN (i) : 0 ≤ N i := apply_nonneg _ _
  let E : A.centers → ℝ := fun i => 2^m * N i
  have hE (i) : 0 ≤ E i := mul_nonneg (by positivity) (hN i)
  let E₀ := ∑ i : A.centers, E i
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun i _ => hE i)
  refine ⟨D*E₀,mul_nonneg hD hE₀,?_⟩
  intro f hf s C hs hs1 hC hb
  let ψ : A.centers → SmallModes.Base → ℝ := fun i => (χ i) ∘ planeCoordinateIsometry.symm
  let g : A.centers → SmallModes.Base → Tensor := fun i x => ψ i x • f i x
  have hψ (i) : ContDiff ℝ ∞ (ψ i) := (χ i).contDiff.comp planeCoordinateIsometry.symm.contDiff
  have hg (i) : ContDiff ℝ ∞ (g i) := (hψ i).smul (hf i)
  have hψsp (i) : tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' U i := by
    apply (show tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' tsupport (χ i) from ?_).trans
      (preimage_mono (hχU i))
    apply closure_minimal _ ((isClosed_tsupport (χ i)).preimage planeCoordinateIsometry.symm.continuous)
    intro x hx
    exact subset_tsupport (χ i) hx
  have hψb (i) : WeightedEstimates.WeightedBound univ s m (N i) (ψ i) :=
    weightedBound_comp_isometry planeCoordinateIsometry.symm (χ i).contDiff
      ((weightedBound_of_supportedSeminorm (1 : ℝ≥0) m (χ i)).shrink_scale hs.le hs1)
  have hgb (i) : WeightedEstimates.WeightedBound univ s m (E i*C) (g i) := by
    let V := planeCoordinateIsometry.symm ⁻¹' U i
    have hV : IsOpen V := (hU i).preimage planeCoordinateIsometry.symm.continuous
    have hprod := ((hψb i).restrict_open hV).smul_real hV.uniqueDiffOn hs.le (hN i) hC
      (hψ i).contDiffOn (hf i).contDiffOn (hb i)
    exact hprod.extend_support hV
      ((tsupport_smul_subset_left (ψ i) (f i)).trans (hψsp i)) (mul_nonneg (hE i) hC)
  have hglobal (i) : WeightedEstimates.WeightedBound univ s m (E₀*C) (g i) := by
    apply (hgb i).mono_const
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)) hC
  have hout := hd g s (E₀*C) hs hs1 (mul_nonneg hE₀ hC) hg hglobal
  have heq : A.tensorPlaneRestore g = A.tensorPlaneRestore f := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ tsupport (A.outer i)
    · have hχp := hχone i p hp
      change A.outer i p • (A.tensorTriv i).symmL ℝ p
        (fiberFromThree ((χ i) (planeCoordinateIsometry.symm
          (planeCoordinateIsometry (chart (i : M) p))) • f i
            (planeCoordinateIsometry (chart (i : M) p)))) = _
      simp only [planeCoordinateIsometry.symm_apply_apply,hχp,one_smul]
      rfl
    · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [bundleRestore,hz,zero_smul]
  rw [heq] at hout
  simpa only [mul_assoc] using hout

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedMultilinearVariations
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product bounds for non-normalized variation maps. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression WeightedEstimates

namespace MixedExpression

lemma rescale_succ (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) (i : Fin 3) :
    rescale G c i.succ = fun p => c i • G i.succ p := by
  fin_cases i <;> rfl

lemma rescale_inverse (G : Fin 4 → Base → Space) (C : Fin 3 → ℝ)
    (hC : ∀ i, C i ≠ 0) : rescale (rescale G (fun i => (C i)⁻¹)) C = G := by
  funext i p
  fin_cases i <;> simp [rescale, smul_smul, hC]

end MixedExpression
namespace Expression

/-- Bounds for the first three actual variations, linear in each participating
map bound and with a single accuracy-independent scale exponent. -/
theorem compact_multilinear_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ) (C : Fin 3 → ℝ),
      0 < s → s ≤ 1 → (∀ i, 0 < C i) →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) (C i) (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            s ^ (e.loss + 6)) (fun p => (e.variations i).eval G (p, t)) := by
  obtain ⟨D, hD, hb⟩ := e.compact_three_variation_bound hU hO hK hKO he m B hB
  refine ⟨D, hD, ?_⟩
  intro G s C hs hs1 hC hG hGK hGb hHb t ht i
  let H := rescale G (fun j => (C j)⁻¹)
  have hH := rescale_smooth hG (fun j => (C j)⁻¹)
  have hunit : ∀ j : Fin 3, WeightedBound U s (m + e.order) 1 (H j.succ) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hG j.succ).contDiffOn (C j)⁻¹
    simpa only [H, rescale_succ, abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hnorm := hb H s hs hs1 hH hGK hGb hunit t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heval : (fun p => (e.variations i).eval G (p, t)) =
      (fun p => W • (e.variations i).eval H (p, t)) := by
    funext p
    have hr := rescale_inverse G C (fun j => ne_of_gt (hC j))
    have hv := e.variations_rescale hH C (p, t) i
    rw [hr] at hv
    exact hv
  rw [heval]
  have hsmooth := MixedExpression.parameter_smooth hH
    (fun p hp => hKO (hGK hp)) (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
  have h := hnorm.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos hW]
  ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTaylorBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-power cubic remainder bound for the actual polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression ParameterTaylor SmoothParameterIntegral WeightedEstimates

/-- The third variation controls the nonlinear remainder, with an exponent
independent of the requested output derivative order. -/
theorem compact_taylorRemainder_bound {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q) (e : Expression) (he : e.SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 < C → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + e.order) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + e.order) C H →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * C ^ 3 / s ^ (e.loss + 6) / 2) (e.taylorRemainder G H θ) := by
  obtain ⟨D, hD, hd⟩ := e.compact_multilinear_variation_bound hU isOpen_univ hQ
    (Set.subset_univ Q) he m B hB
  refine ⟨D, hD, ?_⟩
  intro G H s C hs hs1 hC hG hH hGQ hGb hHb θ hθ
  apply weighted_taylorRemainder he hG hH θ hU hs
    (show 0 ≤ D * C ^ 3 / s ^ (e.loss + 6) by positivity) m
  intro j hj p hp t ht
  let V := varyBase (diagonalFamily G H) H t
  have hV : ∀ i, ContDiff ℝ ∞ (V i) :=
    varyBase_smooth (diagonalFamily_smooth hG hH) hH t
  have hVQ : Set.MapsTo (lowJet (V 0)) U Q := hGQ t ht
  have hVb : WeightedBound U s (m + e.order) B (lowJet (V 0)) := hGb t ht
  have hdirs : ∀ i : Fin 3, WeightedBound U s (m + e.order) C (V i.succ) := by
    intro i
    simpa only [V, varyBase_other _ _ _ (Fin.succ_ne_zero i), diagonalFamily_succ] using hHb
  have hv := hd V s (fun _ => C) hs hs1 (fun _ => hC) hV hVQ hVb hdirs θ hθ 2
  change WeightedBound U s m (D * (C * C * C) / s ^ (e.loss + 6))
    (fun p => (e.variations 2).eval V (p, θ)) at hv
  have hcubic : D * (C * C * C) / s ^ (e.loss + 6) = D * C ^ 3 / s ^ (e.loss + 6) := by ring
  rw [hcubic] at hv
  have hval := hv j hj p hp
  have hJ := eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH
    (e.variations_smoothCoeffs isOpen_univ he 2) θ
  have hslice := hJ.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  change ContDiff ℝ ∞ (fun p => (e.variations 2).eval V (p, θ)) at hslice
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    ((hslice.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp] at hval
  exact hval

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbationTaylorBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite polynomial perturbation has a cubic nonlinear remainder with
one fixed scale loss. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ParameterTaylor WeightedEstimates

variable {n : ℕ}

lemma expression_taylorRemainder_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.taylorRemainder G H θ) := by
  rw [← Expression.cubicRemainder_affine he hG hH θ]
  exact cubicRemainder_smooth (Expression.affinePolynomial_smooth he hG hH θ)

theorem compact_taylorRemainder_bound {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs Set.univ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C ε : ℝ),
      0 < s → s ≤ 1 → 0 < C → 0 ≤ ε → ε ≤ 1 → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + order P) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + order P) C H →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * ε * C ^ 3 / s ^ loss P) (taylorRemainder P ε G H θ) := by
  classical
  have hex := fun l => (P l).compact_taylorRemainder_bound hU hQ (hP l) m B hB
  choose D hD hd using hex
  refine ⟨∑ l, D l / 2, Finset.sum_nonneg (fun l _ => div_nonneg (hD l) (by norm_num)), ?_⟩
  intro G H s C ε hs hs1 hC hε hε1 hG hH hGQ hGb hHb θ hθ
  have hval (l : Fin n) : WeightedBound U s m (D l / 2 * ε * C ^ 3 / s ^ loss P)
      (fun p => ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p) := by
    have hDl := hD l
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hp := hd l G H s C hs hs1 hC hG hH hGQ
      (fun t ht => (hGb t ht).mono_order (Nat.add_le_add_left hl m))
      (hHb.mono_order (Nat.add_le_add_left hl m)) θ hθ
    have hp' : WeightedBound U s m (D l / 2 * C ^ 3 / s ^ loss P)
        ((P l).taylorRemainder G H θ) := by
      apply hp.mono_const
      have hpow := pow_le_pow_of_le_one hs.le hs1
        (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))
      calc
        _ = (D l / 2 * C ^ 3) / s ^ ((P l).loss + 6) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hs _) hpow
    have hsm := expression_taylorRemainder_smooth (hP l) hG hH θ
    have hscaled := hp'.const_smul hU.uniqueDiffOn hsm.contDiffOn (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have hpow : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l / 2 * C ^ 3 / s ^ loss P) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l / 2 * ε * C ^ 3 / s ^ loss P)
    (fun l p => ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p)
    (fun l _ => (contDiffOn_const.mul
      (expression_taylorRemainder_smooth (hP l) hG hH θ).contDiffOn)) (fun l _ => hval l)
  change WeightedBound U s m ((∑ l, D l / 2) * ε * C ^ 3 / s ^ loss P)
    (fun p => ∑ l, ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p)
  simpa only [← Finset.sum_div, ← Finset.sum_mul] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRealVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common tensor bounds for the actual mixed quadratic term and cubic
Taylor remainder. The exponent does not depend on the correction depth. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma tensorTaylorRemainder_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorTaylorRemainder P ε G H t) := by
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε ^ (l.val + 1) * (P k l).taylorRemainder G H t p)
  exact ContDiff.sum fun l _ => contDiff_const.mul
    (expression_taylorRemainder_smooth (hP k l) hG hH t)

theorem tensorTaylorRemainder_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H : Base → Space) (s ε C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + tensorOrder P) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + tensorOrder P) C H → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 3 / s ^ tensorLoss P)
          (tensorTaylorRemainder P ε G H t) := by
  have hex (k : Fin 3) := compact_taylorRemainder_bound hU hQ (P k) (hP k) m B hB
  choose E hE he using hex
  refine ⟨∑ k, E k, Finset.sum_nonneg (fun k _ => hE k), ?_⟩
  intro G H s ε C hs hs1 hε hε1 hC hG hH hGQ hGb hHb t ht
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · exact contDiffOn_pi.mp (tensorTaylorRemainder_smooth hP hG hH ε t).contDiffOn
  · intro k
    have hEk := hE k
    have ho : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hl : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G H s C ε hs hs1 hC hε hε1 hG hH hGQ
      (fun t ht => (hGb t ht).mono_order (Nat.add_le_add_left ho m))
      (hHb.mono_order (Nat.add_le_add_left ho m)) t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C ^ 3 / s ^ tensorLoss P :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 hl)
      _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateNonlinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate realizations of the actual bilinear and cubic polynomial
terms in the nonlinear increment identity. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateTaylorRemainder_eq_tensor {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X : RealModes.RField 4) :
    coordinateTaylorRemainder P ε G X =
      tensorTaylorRemainder P ε G (X ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm := rfl

theorem coordinateTaylorRemainder_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X : RealModes.RField 4)
      (s ε C : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p))) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + tensorOrder P) B
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p)))) →
      WeightedBound Set.univ s (m + tensorOrder P) C X →
        WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m
          (E * ε * C ^ 3 / s ^ tensorLoss P) (coordinateTaylorRemainder P ε G X) := by
  obtain ⟨E,hE,he⟩ := tensorTaylorRemainder_bound hU hQ P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G X s ε C hs hs1 hε hε1 hC hG hX hGQ hGb hXb
  have hx := weightedBound_comp_isometry planeCoordinateIsometry hX hXb
  have hb := he G (X ∘ planeCoordinateIsometry) s ε C hs hs1 hε hε1 hC hG
    (hX.comp planeCoordinateIsometry.contDiff) hGQ hGb
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hx j hj p (Set.mem_univ p)) 0 (by constructor <;> norm_num)
  rw [coordinateTaylorRemainder_eq_tensor]
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU
    (tensorTaylorRemainder_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff) ε 0) hb

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNonlinearScales
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smallness hypotheses convert the polynomial mixed and cubic terms
to the common delta-cubed/wavelength error scale. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma polynomial_cubic_scale {E ε A δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (A * δ * τ) ^ 3 / τ ^ p ≤ E * A ^ 3 * (δ ^ 3 / τ) := by
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  calc
    _ = (E * A ^ 3 * (δ ^ 3 / τ)) * ((ε / τ ^ p) * τ ^ 4) := by field_simp
    _ ≤ (E * A ^ 3 * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (pow_nonneg hτ.le _) hsmall).trans hτ4
    _ = _ := mul_one _

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledNonlinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed and cubic nonlinear errors at the scales of the small
increment construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

theorem scaled_coordinate_taylor_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X : RealModes.RField 4)
      (τ ε δ A : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → 0 < A →
      ε / τ ^ tensorLoss P ≤ 1 → ContDiff ℝ ∞ G → ContDiff ℝ ∞ X →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p))) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U τ (m + tensorOrder P) B₀
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p)))) →
      WeightedBound Set.univ τ (m + tensorOrder P) (A * δ * τ) X →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) τ m
        (E * A ^ 3 * (δ ^ 3 / τ)) (coordinateTaylorRemainder P ε G X) := by
  obtain ⟨E,hE,he⟩ := coordinateTaylorRemainder_bound hU hQ P hP m B₀ hB₀
  refine ⟨E,hE,?_⟩
  intro G X τ ε δ A hτ hτ1 hε hε1 hδ hA hsmall hG hX hGQ hGb hXb
  exact (he G X τ ε (A * δ * τ) hτ hτ1 hε hε1 (by positivity) hG hX hGQ hGb hXb).mono_const
    (polynomial_cubic_scale hE hε hA.le hδ.le hτ hτ1 hsmall)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRemainderBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasRemainderFiberNormed_r5d62f7_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasRemainderFiberSpace_r5d62f7_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasRemainderDualAdd_r5d62f7_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasRemainderDualSmul_r5d62f7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)



local instance atlasRemainderSectionNormed_r5d62f7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasRemainderSectionSpace_r5d62f7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The cubic Taylor remainder of the actual global polynomial metric. -/
theorem atlas_polynomial_remainder_bound_oai {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B C : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) (hC : ∀ i, 0 < C i) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → MapsTo
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x)) (U i) (Q i)) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → WeightedEstimates.WeightedBound (U i) τ
        (m+tensorOrder (P i)) (B i)
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x))) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i))
        (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
      A.TensorWeightedBound τ m (E*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F X) := by
  classical
  choose E hE he using fun i : A.centers => scaled_coordinate_taylor_bound (hU i) (hQ i)
    (P i) (hP i) m (B i) (hB i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound_on_outer U hU houter m
  let S := ∑ i : A.centers, E i*(C i)^3
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hE i) (pow_nonneg (hC i).le _))
  refine ⟨D*S,mul_nonneg hD hS,?_⟩
  intro F X hF hX τ ε δ hτ hτ1 hε hε1 hδ hsmall hseg hsegb hXb
  have hlocal (i : A.centers) := he i (A.jetChartMap i F)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) τ ε δ (C i)
    hτ hτ1 hε hε1 hδ (hC i) (hsmall i) (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
  have hbound (i : A.centers) : WeightedEstimates.WeightedBound
      (planeCoordinateIsometry.symm ⁻¹' U i) τ m (S*(δ^3/τ))
      (coordinateTaylorRemainder (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) := by
    have hb := hlocal i
      (by simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hseg i)
      (by simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hsegb i)
      (hXb i)
    exact hb.mono_const (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => mul_nonneg (hE j) (pow_nonneg (hC j).le _))
        (Finset.mem_univ i)) (div_nonneg (pow_nonneg hδ.le _) hτ.le))
  have hsmooth (i : A.centers) : ContDiff ℝ ∞
      (coordinateTaylorRemainder (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) := by
    exact (tensorTaylorRemainder_smooth (hP i) (A.jetChartMap_smooth i hF)
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
        planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff
  have hh := hd _ hsmooth τ (S*(δ^3/τ)) hτ hτ1
    (mul_nonneg hS (div_nonneg (pow_nonneg hδ.le _) hτ.le)) hbound
  simpa only [atlasPolynomialRemainder,mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound_oai.{u_1}
