-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:49:23.985231+00:00
-- url     : https://prove2.me/submissions/dcda1d51-1f8e-4367-991a-6b165b59b082

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma jet_cons (G : Base → Space) (v : Fin 2) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet G (v :: w) a p = fderiv ℝ (jet G w a) p (coordinateVector v) := rfl

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

lemma lowBasis_expansion (J : LowJet) : J = ∑ i : LowIndex, J i • lowBasis i := by
  ext i
  simp [lowBasis, Pi.single_apply]

/-- Differentiating a low-jet coefficient introduces only the next coordinate
jet, linearly, with new smooth low-jet coefficients. -/
theorem coefficient_chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet → E}
    (v : Fin 2) (p : Base) (hc : DifferentiableAt ℝ c (lowJet G p)) :
    fderiv ℝ (fun q => c (lowJet G q)) p (coordinateVector v) =
      ∑ i : LowIndex, (lowDerivative G v p i) • fderiv ℝ c (lowJet G p) (lowBasis i) := by
  have hQ := (lowJet_smooth hG).differentiable (by simp) p
  change fderiv ℝ (c ∘ lowJet G) p (coordinateVector v) = _
  rw [fderiv_comp p hc hQ, ContinuousLinearMap.comp_apply, lowJet_derivative hG]
  conv_lhs => rw [lowBasis_expansion (lowDerivative G v p), map_sum]
  simp only [map_smul]

end ClosedSurfaceR4.JetPolynomial

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma eval_mapCoeff_mul (e : Expression) (G : Base → Space) (c : LowJet × ℝ → ℝ)
    (z : Base × ℝ) :
    (e.mapCoeff (fun d x => c x * d x)).eval G z = c (lowJet G z.1, z.2) * e.eval G z := by
  induction e with
  | coeff d => rfl
  | atom w a e ih => simp only [mapCoeff, eval, ih] <;> ring
  | add e f ihe ihf => simp only [mapCoeff, eval, ihe, ihf] <;> ring

lemma eval_mul (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.mul f).eval G z = e.eval G z * f.eval G z := by
  induction e with
  | coeff c => exact eval_mapCoeff_mul f G c z
  | atom w a e ih => simp only [mul, eval, ih] <;> ring
  | add e g ihe ihg => simp only [mul, eval, ihe, ihg] <;> ring

lemma order_mul_le (e f : Expression) : (e.mul f).order ≤ max e.order f.order := by
  induction e with
  | coeff c => simp only [mul, order_mapCoeff, order]; exact le_max_right _ _
  | atom w a e ih => simp only [mul, order] at *; omega
  | add e g ihe ihg => simp only [mul, order] at *; omega

lemma smoothCoeffs_map {O : Set LowJet} (e : Expression) (f)
    (hf : ∀ c, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (f c) (O ×ˢ Set.univ))
    (he : e.SmoothCoeffs O) : (e.mapCoeff f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact hf c he
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma smoothCoeffs_mul {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.mul f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact smoothCoeffs_map f _ (fun d hd => he.mul hd) hf
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedPhaseExpressions
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-scale estimates for the actual higher-jet expressions, with a varying
angular phase. The slow-jet loss is independent of the output derivative order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_pair {U : Set Base} (hU : IsOpen U)
    {Q : Base → LowJet} {t : Base → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (ht : ContDiffOn ℝ ∞ t U) {s B P : ℝ} {m : ℕ} (hs : 0 < s)
    (hb : WeightedBound U s m B Q) (hp : WeightedBound U s m P t) :
    WeightedBound U s m (B + P) (fun p => (Q p, t p)) := by
  have hleft := hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hright := hp.linear hU.uniqueDiffOn hs.le ht (ContinuousLinearMap.inr ℝ LowJet ℝ)
  simp only [ContinuousLinearMap.norm_inl, ContinuousLinearMap.norm_inr, one_mul,
    Function.comp_def, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply] at hleft hright
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const)
      (contDiffOn_const.prodMk ht) hright

namespace Expression

lemma phase_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space} {t : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (ht : ContDiffOn ℝ ∞ t U) {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t p)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk ht)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

/-- The constant is uniform over the open spatial domain and the phase.
The two scales are kept separate: differentiation is weighted at `τ`, whereas
higher jets only cost powers of the slower scale `s`. -/
theorem compact_phase_bound {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ)
    (B P : ℝ) (hB : 1 ≤ B) (hP : 1 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set Base), IsOpen U →
      ∀ (G : Base → Space) (t : Base → ℝ) (s τ : ℝ),
      0 < τ → τ ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      ContDiffOn ℝ ∞ t U → Set.MapsTo (lowJet G) U K →
      Set.MapsTo t U (Set.Icc (-1) 2) →
      WeightedBound U s (m + e.order) B (lowJet G) →
      WeightedBound U τ m P t →
      WeightedBound U τ m (D / s ^ e.loss) (fun p => e.eval G (p, t p)) := by
  induction e with
  | coeff c =>
    have hcompact : IsCompact (K ×ˢ Set.Icc (-1 : ℝ) 2) := hK.prod isCompact_Icc
    have hsub : K ×ˢ Set.Icc (-1 : ℝ) 2 ⊆ O ×ˢ Set.univ :=
      fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
    obtain ⟨D, hD, hd⟩ := compact_coefficient_bound
      (hO.prod isOpen_univ).uniqueDiffOn hcompact hsub he m
    refine ⟨(m.factorial : ℝ) * D * (B + P) ^ m, by positivity, ?_⟩
    intro U hU G t s τ hτ hτs _ hG ht hGK htk hb hp
    have hb' := (hb.mono_order (by simp [order] : m ≤ m + (Expression.coeff c).order)).shrink_scale hτ.le hτs
    have hpq := weighted_pair hU (lowJet_smooth hG).contDiffOn ht hτ hb' hp
    have hh := hpq.comp hU.uniqueDiffOn (hO.prod isOpen_univ).uniqueDiffOn
      hτ (by linarith : 1 ≤ B + P) (zero_le_one.trans hD)
      ((lowJet_smooth hG).contDiffOn.prodMk ht) he
      (fun x hx => ⟨hKO (hGK hx), Set.mem_univ _⟩)
      (fun j hj x hx => hd j hj _ ⟨hGK hx, htk hx⟩)
    simpa only [loss, pow_zero, div_one, eval, Function.comp_def] using hh
  | atom w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro U hU G t s τ hτ hτs hs1 hG ht hGK htk hb hp
    have hs : 0 < s := hτ.trans_le hτs
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hx => hKO (hGK hx)
    have hj := (weighted_actual_jet hU hG hs (zero_le_one.trans hB) m w a
      (hb.mono_order (by simp only [order]; omega))).shrink_scale hτ.le hτs
    have hb' := hd U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hh := hj.mul_real hU.uniqueDiffOn hτ.le (by positivity) (by positivity)
      (jet_smooth hG w a).contDiffOn (phase_smooth hG hQ ht (e := e) he) hb'
    convert hh using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro U hU G t s τ hτ hτs hs1 hG ht hGK htk hb hp
    have hs : 0 < s := hτ.trans_le hτs
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hx => hKO (hGK hx)
    have hd' := hd U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hc' := hc U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hd'' : WeightedBound U τ m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t p)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U τ m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t p)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hτ.le
      (phase_smooth hG hQ ht (e := e) he.1) (phase_smooth hG hQ ht (e := f) he.2) hc''

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma eval_sumList {ι : Type*} (l : List ι) (f : ι → Expression) (G : Base → Space)
    (z : Base × ℝ) : (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (hf : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

lemma eval_lowFactor (v : Fin 2) (i : LowIndex) (G : Base → Space) (z : Base × ℝ) :
    (lowFactor v i).eval G z = lowDerivative G v z.1 i := by
  cases i with
  | inl i => rfl
  | inr i => simp [lowFactor, eval, lowDerivative]

lemma order_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).order ≤ 3 := by
  cases i with
  | inl i => simp [lowFactor, order]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, order, List.length_cons]
    omega

lemma smoothCoeffs_lowFactor (O : Set LowJet) (v : Fin 2) (i : LowIndex) :
    (lowFactor v i).SmoothCoeffs O := by
  cases i with
  | inl i => exact contDiffOn_const
  | inr i => exact contDiffOn_const

lemma smoothCoeffs_slow {O : Set LowJet} (hO : IsOpen O) (v : Fin 2)
    {e : Expression} (he : e.SmoothCoeffs O) : (e.slow v).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact smoothCoeffs_mul (smoothCoeffs_lowFactor O v i)
      (LocalPeriodicCalculus.slow_smooth hO he (lowBasis i))
  | atom w a e ih => exact ⟨he, ih he⟩
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

lemma order_slow_le (v : Fin 2) (e : Expression) :
    (e.slow v).order ≤ max 3 (e.order + 1) := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ _ (by simp [order])
    intro i _
    exact (order_mul_le _ _).trans (max_le (order_lowFactor v i) (by simp [order]))
  | atom w a e ih => simp only [slow, order, List.length_cons] at *; omega
  | add e f ihe ihf => simp only [slow, order] at *; omega

lemma coefficient_chain_rule_joint {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet × ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) (v : Fin 2) (p : Base)
    (hp : lowJet G p ∈ O) (t : ℝ) :
    fderiv ℝ (fun q => c (lowJet G q, t)) p (coordinateVector v) =
      ∑ i : LowIndex, lowDerivative G v p i * slowDerivative c (lowBasis i) (lowJet G p, t) := by
  have hs : DifferentiableAt ℝ (fun Q : LowJet => c (Q, t)) (lowJet G p) :=
    ((hc.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp _
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [smul_eq_mul, LocalPeriodicCalculus.fderiv_slice hO hc hp] using
    coefficient_chain_rule hG v p hs

/-- The syntactic derivative evaluates to the genuine derivative on every
open region where the low-jet coefficients are smooth. -/
theorem eval_slow {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {e : Expression} (he : e.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (e.slow v).eval G (p, t) = fderiv ℝ (fun q => e.eval G (q, t)) p (coordinateVector v) := by
  induction e with
  | coeff c =>
    rw [slow, eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [eval_mul, eval_lowFactor, eval]
    exact (coefficient_chain_rule_joint hO hG he v p (hQ hp) t).symm
  | atom w a e ih =>
    have hj := (jet_smooth hG w a).differentiable (by simp) p
    have he' : DifferentiableAt ℝ (fun q => e.eval G (q, t)) p :=
      (((eval_smooth hG hQ (e := e) he).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simp only [slow, eval, ih he]
    rw [fderiv_fun_mul hj he']
    simp only [add_apply, smul_apply, smul_eq_mul,
      jet_cons]
    ring
  | add e f ihe ihf =>
    have hd (g : Expression) (hg : g.SmoothCoeffs O) :
        DifferentiableAt ℝ (fun q => g.eval G (q, t)) p :=
      (((eval_smooth hG hQ hg).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [slow, eval, fderiv_fun_add (hd e he.1) (hd f he.2),
      add_apply] using congrArg₂ (· + ·) (ihe he.1) (ihf he.2)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular derivatives, averaging, and normalized primitives act only on
smooth low-jet coefficients, preserving polynomial jet order and scale loss. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma eval_slice_smooth {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) :
    ContDiff ℝ ∞ (fun t => e.eval G (p, t)) := by
  induction e with
  | coeff c => exact LocalPeriodicCalculus.smooth_slice hO he hp
  | atom w a e ih =>
    change ContDiff ℝ ∞ (fun t => jet G w a p * e.eval G (p, t))
    exact contDiff_const.mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma smoothCoeffs_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.angle.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => LocalPeriodicCalculus.angle_smooth hO hc) he

lemma eval_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.angle.eval G (p, t) = deriv (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => exact (LocalPeriodicCalculus.angle_hasDerivAt hO he hp t).deriv.symm
  | atom w a e ih =>
    change jet G w a p * e.angle.eval G (p, t) =
      deriv (fun s => jet G w a p * e.eval G (p, s)) t
    rw [deriv_const_mul _ ((eval_slice_smooth hO (e := e) he G hp).differentiable (by simp) t),
      ih he]
  | add e f ihe ihf =>
    change e.angle.eval G (p, t) + f.angle.eval G (p, t) =
      deriv (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [deriv_fun_add ((eval_slice_smooth hO he.1 G hp).differentiable (by simp) t)
      ((eval_slice_smooth hO he.2 G hp).differentiable (by simp) t), ihe he.1, ihf he.2]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

namespace VectorExpression

lemma order_slow_le {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (v : Fin 2) : ∀ i, (R.slow v i).order ≤ N + 1 := by
  intro i
  have hi := hR i
  exact (Expression.order_slow_le v (R i)).trans (by omega)

lemma represents_slow {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (v : Fin 2) : Represents G (R.slow v) (U.slow (coordinateVector v)) := by
  intro i p hp t
  rw [slow, Expression.eval_slow hO S.isOpen hG hQ v (hRs i) hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  have heq : (fun x => (R i).eval G (x, t)) =ᶠ[𝓝 p]
      (fun x => L (U.val x (t : CovarianceCorrector.Period))) := by
    filter_upwards [S.isOpen.mem_nhds hp] with x hx
    exact hR i x hx t
  rw [heq.fderiv_eq]
  have hU : DifferentiableAt ℝ (fun x => U.val x (t : CovarianceCorrector.Period)) p :=
    ((U.smooth.contDiffAt ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (L ∘ fun x => U.val x (t : CovarianceCorrector.Period)) p
    (coordinateVector v) = _
  rw [(L.hasFDerivAt.comp p hU.hasFDerivAt).fderiv]
  rw [Family.slow_apply U (coordinateVector v) hp t,
    ← LocalPeriodicCalculus.fderiv_slice S.isOpen U.smooth hp]
  rfl

lemma represents_angle {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.angle U.angle := by
  intro i p hp t
  rw [angle, Expression.eval_angle hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (L.hasFDerivAt.comp_hasDerivAt t (U.angle_hasDerivAt hp t)).deriv

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma fastValue_smooth (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiffOn ℝ ∞ (U.fastValue ℓ z) O :=
  U.smooth.comp (contDiffOn_id.prodMk (ℓ.contDiff.div_const z).contDiffOn)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FastPhaseBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform weighted bounds after substituting the fast circle phase. Local
real lifts keep the constants independent of the number of oscillations. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open_domain {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hb : WeightedBound U s m C f) : WeightedBound V s m C f := by
  intro j hj p hp
  rw [iteratedFDerivWithin_of_isOpen j hV hp]
  have h := hb j hj p (hVU hp)
  rwa [iteratedFDerivWithin_of_isOpen j hU (hVU hp)] at h

lemma weighted_shifted_phase {U : Set E} (hU : IsOpen U) (ℓ : E →L[ℝ] ℝ)
    (c : ℝ) {z P : ℝ} (hz : 0 < z) (hP : 2 ≤ P) (hℓ : ‖ℓ‖ ≤ P)
    (ht : Set.MapsTo (fun p => ℓ p / z - c) U (Set.Icc (-1) 2)) (m : ℕ) :
    WeightedBound U z m P (fun p => ℓ p / z - c) := by
  intro j _ p hp
  rw [iteratedFDerivWithin_of_isOpen j hU hp]
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [(ht hp).1], (ht hp).2⟩).trans hP
  | succ n =>
    have hd : fderiv ℝ (fun p => ℓ p / z - c) = fun _ => z⁻¹ • ℓ := by
      funext q
      simp only [fderiv_sub_const]
      have he : (fun p => ℓ p / z) = ⇑(z⁻¹ • ℓ) := by
        funext x
        simp [div_eq_mul_inv, mul_comm]
      rw [he, ContinuousLinearMap.fderiv]
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero, pow_one]
      calc
        z * ‖z⁻¹ • ℓ‖ = ‖ℓ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
          field_simp
        _ ≤ P := hℓ
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, mul_zero] <;> linarith

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates CovarianceCorrector

/-- A periodic function represented by an actual jet expression retains its
slow-scale loss after evaluation at a fast linear phase. -/
theorem compact_periodic_fast_bound {S : Set Base} (hS : IsOpen S) {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + e.order) B (lowJet G) →
      ∀ (H : Base → Period → ℝ),
        (∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = H p (t : Period)) →
        WeightedBound S z m (D / s ^ e.loss)
          (fun p => H p ((ℓ p / z : ℝ) : Period)) := by
  obtain ⟨D, hD, hd⟩ := Expression.compact_phase_bound hO hK hKO
    e he m B (2 + ‖ℓ‖) hB (by linarith [norm_nonneg ℓ])
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hb H hR j hj p hp
  let a : ℝ := AddCircle.equivIco 1 0 ((ℓ p / z : ℝ) : Period)
  have ha : a ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 ((ℓ p / z : ℝ) : Period)).property
  have hca : (a : Period) = ((ℓ p / z : ℝ) : Period) := AddCircle.coe_equivIco
  let c : ℝ := ℓ p / z - a
  let t : Base → ℝ := fun q => ℓ q / z - c
  have hcz : (c : Period) = 0 := by
    rw [show c = ℓ p / z - a from rfl, AddCircle.coe_sub, hca, sub_self]
  have hct (q : Base) : (t q : Period) = ((ℓ q / z : ℝ) : Period) := by
    rw [show t q = ℓ q / z - c from rfl, AddCircle.coe_sub, hcz, sub_zero]
  have ht : ContDiff ℝ ∞ t := (ℓ.contDiff.div_const z).sub contDiff_const
  let V : Set Base := (S : Set Base) ∩ t ⁻¹' Set.Ioo (-1) 2
  have hV : IsOpen V := hS.inter (isOpen_Ioo.preimage ht.continuous)
  have hVS : V ⊆ S := Set.inter_subset_left
  have hpV : p ∈ V := by
    refine ⟨hp, ?_⟩
    change -1 < ℓ p / z - (ℓ p / z - a) ∧ ℓ p / z - (ℓ p / z - a) < 2
    constructor <;> linarith [ha.1, ha.2]
  have htV : Set.MapsTo t V (Set.Icc (-1) 2) := fun _ hx => ⟨hx.2.1.le, hx.2.2.le⟩
  have hbt := weighted_shifted_phase hV ℓ c hz (by linarith [norm_nonneg ℓ])
    (by linarith : ‖ℓ‖ ≤ 2 + ‖ℓ‖) htV m
  have hh := hd V hV G t s z hz hzs hs1 hG ht.contDiffOn
    (fun _ hx => hGK (hVS hx)) htV (hb.restrict_open_domain hS hV hVS) hbt
  have heq : (fun q => e.eval G (q, t q)) =ᶠ[𝓝 p]
      (fun q => H q ((ℓ q / z : ℝ) : Period)) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [hR q hq (t q), hct q]
  have hjet := (heq.iteratedFDeriv ℝ j).self_of_nhds
  have h := hh j hj p hpV
  rw [iteratedFDerivWithin_of_isOpen j hV hpV, hjet] at h
  rwa [iteratedFDerivWithin_of_isOpen j hS hp]


end ClosedSurfaceR4.JetPolynomial.Expression

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

/-- Each actual periodic coefficient has a fast-scale bound with the same
slow-scale loss as its jet polynomial. -/
theorem compact_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : VectorExpression) (hRs : R.SmoothCoeffs O) (i : Fin 4)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (R i).order) B (lowJet G) →
      ∀ (U : Family S R4), Represents G R U →
        WeightedBound S z m (D / s ^ (R i).loss)
          (fun p => U.fastValue ℓ z p i) := by
  obtain ⟨D, hD, hd⟩ := Expression.compact_periodic_fast_bound S.isOpen hO hK hKO
    (R i) (hRs i) ℓ m B hB
  exact ⟨D, hD, fun G s z hz hzs hs1 hG hGK hb U hR =>
    hd G s z hz hzs hs1 hG hGK hb (fun p t => U.val p t i) (hR i)⟩

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteFastBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fast-scale estimates for finite collections of the actual
periodic correctors, and for their finite oscillatory sum. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

/-- Finitely many coefficients admit one common prefactor and one common
scale loss, also in the Euclidean norm on the target. -/
theorem compact_finite_fast_bound {ι : Type*} [Fintype ι]
    {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ι → VectorExpression) (hRs : ∀ a, (R a).SmoothCoeffs O)
    (N d : ℕ) (hN : ∀ a i, (R a i).order ≤ N) (hd : ∀ a i, (R a i).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (U : ι → Family S R4), (∀ a, Represents G (R a) (U a)) → ∀ a,
        WeightedBound S z m (D / s ^ d) ((U a).fastValue ℓ z) := by
  classical
  have hex := fun a : ι × Fin 4 => compact_fast_bound (S := S) hO hK hKO (R a.1) (hRs a.1) a.2 ℓ m B hB
  choose C hC hc using hex
  let C₀ : ℝ := ∑ a : ι × Fin 4, C a
  let L : (Fin 4 → ℝ) →L[ℝ] R4 := (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap
  refine ⟨‖L‖ * C₀, mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _ => hC a), ?_⟩
  intro G s z hz hzs hs1 hG hGK hb U hrep a
  have hs : 0 < s := hz.trans_le hzs
  have hcoord (i : Fin 4) :
      WeightedBound S z m (C₀ / s ^ d) (fun p => (U a).fastValue ℓ z p i) := by
    have hi := hc (a, i) G s z hz hzs hs1 hG hGK
      (hb.mono_order (Nat.add_le_add_left (hN a i) m)) (U a) (hrep a)
    apply hi.mono_const
    calc
      C (a, i) / s ^ (R a i).loss ≤ C (a, i) / s ^ d :=
        div_le_div_of_nonneg_left (hC _) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (hd a i))
      _ ≤ C₀ / s ^ d := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ (a, i))) (pow_nonneg hs.le _)
  have hsmooth (i : Fin 4) : ContDiffOn ℝ ∞ (fun p => (U a).fastValue ℓ z p i) S :=
    (show R4 →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.comp_contDiffOn ((U a).fastValue_smooth ℓ z)
  have hp := WeightedBound.pi S.isOpen.uniqueDiffOn hz
    (div_nonneg (Finset.sum_nonneg fun b _ => hC b) (pow_nonneg hs.le _)) hsmooth hcoord
  have hp' := hp.linear S.isOpen.uniqueDiffOn hz.le (contDiffOn_pi.mpr hsmooth) L
  have heq : (L ∘ fun p i => (U a).fastValue ℓ z p i) = (U a).fastValue ℓ z := by
    funext p
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply _
  rw [heq] at hp'
  convert hp' using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CoefficientJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite first and second slow/angular coefficient jets needed by the
primitive's five leading derivative estimates share one fixed scale loss. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

lemma coefficientDerivative_smooth {O : Set LowJet} (hO : IsOpen O) {R : VectorExpression}
    (hR : R.SmoothCoeffs O) (k : Fin 3) : (R.coefficientDerivative k).SmoothCoeffs O := by
  fin_cases k
  · exact fun a => Expression.smoothCoeffs_slow hO 0 (hR a)
  · exact fun a => Expression.smoothCoeffs_slow hO 1 (hR a)
  · exact fun a => Expression.smoothCoeffs_angle hO (hR a)

lemma coefficientDerivative_order {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ a, (R a).order ≤ N) (k : Fin 3) (a : Fin 4) :
    (R.coefficientDerivative k a).order ≤ N+1 := by
  fin_cases k
  · exact order_slow_le hN hR 0 a
  · exact order_slow_le hN hR 1 a
  · change (R a).angle.order ≤ N+1
    rw [Expression.order_angle]
    exact (hR a).trans (Nat.le_succ N)

lemma represents_coefficientDerivative {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O) (hR : Represents G R U)
    (k : Fin 3) : Represents G (R.coefficientDerivative k) (coefficientFamilyDerivative U k) := by
  fin_cases k
  · exact represents_slow hO hG hGO hRs hR 0
  · exact represents_slow hO hG hGO hRs hR 1
  · exact represents_angle hO hGO hRs hR

theorem compact_coefficient_two_jets_oai {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
    (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (ℓ : Base →L[ℝ] ℝ) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
      WeightedBound S s (N+2) B (lowJet G) →
      ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
      ∀ i < L, ∀ k j : Fin 3, ∀ p ∈ S,
        ‖(coefficientFamilyDerivative (U i) k).fastValue ℓ z p‖ ≤ D/s^loss ∧
        ‖(coefficientFamilyDerivative (coefficientFamilyDerivative (U i) k) j).fastValue ℓ z p‖ ≤
          D/s^loss := by
  classical
  let I := Bool × Fin 3 × Fin 3 × Fin L
  let R' : I → VectorExpression := fun a => if a.1 then
    ((R a.2.2.2).coefficientDerivative a.2.1).coefficientDerivative a.2.2.1
    else (R a.2.2.2).coefficientDerivative a.2.1
  have hR's (a : I) : (R' a).SmoothCoeffs O := by
    dsimp only [R']
    split_ifs
    · exact coefficientDerivative_smooth hO
        (coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _) _
    · exact coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _
  have hR'o (a : I) (v : Fin 4) : (R' a v).order ≤ N+2 := by
    dsimp only [R']
    split_ifs
    · exact coefficientDerivative_order (by omega)
        (coefficientDerivative_order hN (hRo _ a.2.2.2.isLt) _) _ v
    · exact (coefficientDerivative_order hN (hRo _ a.2.2.2.isLt) _ v).trans (by omega)
  let loss := Finset.univ.sup (fun a : I => Finset.univ.sup (fun v : Fin 4 => (R' a v).loss))
  have hl (a : I) (v : Fin 4) : (R' a v).loss ≤ loss :=
    (Finset.le_sup (f := fun v : Fin 4 => (R' a v).loss) (Finset.mem_univ v)).trans
      (Finset.le_sup (f := fun a : I => Finset.univ.sup (fun v : Fin 4 => (R' a v).loss))
        (Finset.mem_univ a))
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := compact_finite_fast_bound (S := S) hO hQ hQO R' hR's (N+2) loss hR'o hl ℓ 0 B hB
  refine ⟨D,hD,?_⟩
  intro G s z hz hzs hs1 hG hGQ hb U hrep i hi k j p hp
  have hGO : MapsTo (lowJet G) S O := fun _ hx => hQO (hGQ hx)
  let U' : I → Family S R4 := fun a => if a.1 then
    coefficientFamilyDerivative (coefficientFamilyDerivative (U a.2.2.2) a.2.1) a.2.2.1
    else coefficientFamilyDerivative (U a.2.2.2) a.2.1
  have hrep' (a : I) : Represents G (R' a) (U' a) := by
    dsimp only [R',U']
    split_ifs
    · exact represents_coefficientDerivative hO hG hGO
        (coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _)
        (represents_coefficientDerivative hO hG hGO (hRs _ a.2.2.2.isLt) (hrep _ a.2.2.2.isLt) _) _
    · exact represents_coefficientDerivative hO hG hGO (hRs _ a.2.2.2.isLt) (hrep _ a.2.2.2.isLt) _
  have hh := hd G s z hz hzs hs1 hG hGQ (by simpa only [zero_add] using hb) U' hrep'
  exact ⟨(hh (false,k,j,⟨i,hi⟩)).norm_le hp,(hh (true,k,j,⟨i,hi⟩)).norm_le hp⟩

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets_oai := @OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets_oai
