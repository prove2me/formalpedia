-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:42.726426+00:00
-- url     : https://prove2.me/submissions/3f30ea73-0ecf-495c-9f76-5933fbc9984c

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem primitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (rawPrimitive_hasDerivAt hf x).sub_const _

end ClosedSurfaceR4.PeriodicPrimitive

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

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveOn F S hS hF hm p (s : Period)) (F p (t : Period)) t := by
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

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

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_angle (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) :
    (F.primitive hm).angle = F := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := (F.primitive hm).angle_hasDerivAt hp x
  have he : (fun s : ℝ => (F.primitive hm).val p (s : Period)) =
      fun s : ℝ => primitiveOn F.val O O.isOpen F.smooth hm p (s : Period) := by
    funext s
    exact ofLocal_apply _ _ hp _
  rw [he] at hd
  exact hd.unique (primitiveOn_hasDerivAt _ _ _ _ _ hp x)

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

lemma smoothCoeffs_dot {O : Set LowJet} {R T : VectorExpression}
    (hR : R.SmoothCoeffs O) (hT : T.SmoothCoeffs O) : (R.dot T).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumList
  intro i _
  exact Expression.smoothCoeffs_mul (hR i) (hT i)

lemma order_dot_le {R T : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (hT : ∀ i, (T i).order ≤ N) : (R.dot T).order ≤ N := by
  apply Expression.order_sumList_le _ _ _ hN
  intro i _
  exact (Expression.order_mul_le _ _).trans (max_le (hR i) (hT i))

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.add T) (U + W) := by
  intro i p hp t
  simp only [add, Expression.eval, hR i p hp t, hT i p hp t, Family.add_apply]
  rfl

lemma eval_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (R.dot T).eval G (p, t) = inner ℝ (U.val p (t : CovarianceCorrector.Period))
      (W.val p (t : CovarianceCorrector.Period)) := by
  rw [dot, Expression.eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
    Finset.toList_toFinset]
  simp only [Expression.eval_mul, hR _ p hp t, hT _ p hp t]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin 4, U.val p (t : CovarianceCorrector.Period) i *
    W.val p (t : CovarianceCorrector.Period) i) =
    ∑ i : Fin 4, W.val p (t : CovarianceCorrector.Period) i * U.val p (t : CovarianceCorrector.Period) i
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
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

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

lemma fastValue_smooth (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiffOn ℝ ∞ (U.fastValue ℓ z) O :=
  U.smooth.comp (contDiffOn_id.prodMk (ℓ.contDiff.div_const z).contDiffOn)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

lemma fastValue_fderiv (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ)
    {p : A} (hp : p ∈ O) (v : A) :
    fderiv ℝ (U.fastValue ℓ z) p v =
      (U.slow v).val p ((ℓ p / z : ℝ) : Period) +
        (ℓ v / z) • U.angle.val p ((ℓ p / z : ℝ) : Period) := by
  let T : A →L[ℝ] A × ℝ := (ContinuousLinearMap.id ℝ A).prod (z⁻¹ • ℓ)
  have hT (p : A) : T p = (p, ℓ p / z) := by simp [T, div_eq_mul_inv, mul_comm]
  have hEq : U.fastValue ℓ z =
      (fun w : A × ℝ => U.val w.1 (w.2 : Period)) ∘ T := by
    funext p
    simp only [Function.comp_apply, hT, fastValue]
  have hd : DifferentiableAt ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (T p) := by
    rw [hT]
    exact (U.smooth.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds
      ⟨hp, Set.mem_univ _⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [hEq, fderiv_comp p hd T.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hT]
  change fderiv ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (p, ℓ p / z) (v, ℓ v / z) = _
  have hv : (v, ℓ v / z) = (v, 0) + (ℓ v / z) • ((0 : A), (1 : ℝ)) := by simp
  rw [hv, map_add, map_smul, slow_apply _ _ hp, angle_apply _ hp]
  rfl

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

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

@[simp] lemma eval_scale (a : ℝ) (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.scale a).eval G z = a * e.eval G z := eval_mapCoeff_mul e G (fun _ => a) z

lemma represents_sumFinset {ι : Type*} {S : TopologicalSpace.Opens Base} {G : Base → Space}
    (a : Finset ι) {e : ι → Expression} {U : ι → Family S ℝ}
    (he : ∀ i ∈ a, Represents G (e i) (U i)) :
    Represents G (sumFinset a e) (∑ i ∈ a, U i) := by
  classical
  intro p hp t
  rw [sumFinset, eval_sumList, ← List.sum_toFinset _ a.nodup_toList, Finset.toList_toFinset,
    Family.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => he i hi p hp t)

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma order_sumFinset_le {ι : Type*} (a : Finset ι) (e : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (he : ∀ i ∈ a, (e i).order ≤ N) : (sumFinset a e).order ≤ N := by
  apply order_sumList_le _ _ _ hN
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma represents_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : VectorExpression.Represents G R U)
    (hT : VectorExpression.Represents G T W) : Represents G (R.dot T) (U.inner W) := by
  intro p hp t
  rw [VectorExpression.eval_dot hR hT hp, Family.inner_apply]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate polynomial expressions for the metric coefficients in
the finite oscillatory recursion. Index zero denotes the first correction. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma order_xCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i < r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) (a : Fin 4) :
    (xCoefficient dx U i a).order ≤ 2 * i + 2 := by
  have hp := Expression.order_slow_le dx (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  have hcur := hU i hir a
  change max ((U (i - 1) a).slow dx).order ((U i a).angle).order ≤ _
  rw [Expression.order_angle]
  omega

lemma order_yCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) (a : Fin 4) :
    (yCoefficient dy U i a).order ≤ 2 * i + 1 := by
  have hp := Expression.order_slow_le dy (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  exact hp.trans (by omega)

lemma represents_xCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (xCoefficient dx U i)
      (LocalPeriodicExpansion.xCoefficient (coordinateVector dx) W i) :=
  VectorExpression.represents_add
    (VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx)
    (VectorExpression.represents_angle hO hQ (hUs _) (hU _))

lemma represents_yCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (yCoefficient dy U i)
      (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) W i) :=
  VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dy

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right-hand sides of the finite triangular correction step are actual
higher-jet polynomials. Their maximal jet order is the preceding order plus one. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma smooth_xCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (i : ℕ) :
    (xCoefficient dx U i).SmoothCoeffs O := by
  intro a
  exact ⟨Expression.smoothCoeffs_slow hO dx (hU _ _),
    Expression.smoothCoeffs_angle hO (hU _ _)⟩

lemma smooth_yCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (i : ℕ) :
    (yCoefficient dy U i).SmoothCoeffs O := by
  intro a
  exact Expression.smoothCoeffs_slow hO dy (hU _ _)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionInit
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

omit [FiniteDimensional ℝ E] in
lemma initial_angle : g.initial.angle = g.V - g.V.vectorMean :=
  Family.primitive_angle _ _

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteMetricPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite polynomial metric algebra for the periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma metricPolynomial_eval (n : ℕ) (a b : ℕ → E) (z : ℝ) :
    (metricPolynomial n a b).eval z =
      inner ℝ (vectorPolynomialValue n a z) (vectorPolynomialValue n b z) := by
  simp only [metricPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    vectorPolynomialValue, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- At each degree no larger than the vector degree, the usual convolution
contains every contributing term, with no truncation at either end. -/
lemma metricPolynomial_coeff {n r : ℕ} (hr : r ≤ n) (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r =
      ∑ i ∈ Finset.range (r + 1), inner ℝ (a i) (b (r - i)) := by
  simp only [metricPolynomial, Polynomial.finsetSum_coeff]
  have hrow (i : ℕ) :
      (∑ j ∈ Finset.range (n + 1), (Polynomial.monomial (i + j) (inner ℝ (a i) (b j))).coeff r) =
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
    by_cases hi : i ≤ r
    · rw [ite_eq_left hi]
      have hc : (Polynomial.monomial (i + (r - i))
          (inner ℝ (a i) (b (r - i)))).coeff r = inner ℝ (a i) (b (r - i)) := by
        simp [Nat.add_sub_of_le hi]
      rw [← hc]
      apply Finset.sum_eq_single (r - i)
      · intro j hj hne
        rw [Polynomial.coeff_monomial]
        split_ifs with he
        · omega
        · rfl
      · intro hn
        exfalso
        apply hn
        exact Finset.mem_range.mpr (by omega)
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_monomial]
      split_ifs with he
      · omega
      · rfl
  simp_rw [hrow]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
  calc
    _ = ∑ i ∈ Finset.range (r + 1),
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro i hin hir
      exact ite_eq_right (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hir)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma metricPolynomial_coeff_pos {n r : ℕ} (hr : r ≤ n) (hpos : 0 < r)
    (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r = inner ℝ (a 0) (b r) + inner ℝ (a r) (b 0) +
      ∑ i ∈ Finset.Ico 1 r, inner ℝ (a i) (b (r - i)) := by
  rw [metricPolynomial_coeff hr, Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico (fun i => inner ℝ (a i) (b (r - i))) hpos]
  simp only [Finset.sum_range_one, Nat.sub_zero, Nat.sub_self]
  ring

lemma metricPolynomial_degree (n : ℕ) (a b : ℕ → E) :
    (metricPolynomial n a b).natDegree ≤ 2 * n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  simp only [metricPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hi hj
  rw [Polynomial.coeff_monomial]
  exact ite_eq_right (by omega)

/-- Split the exact metric polynomial at any chosen expansion order. -/
lemma metricPolynomial_expansion (n k : ℕ) (hk : k ≤ 2 * n + 1)
    (a b : ℕ → E) (z : ℝ) :
    inner ℝ (vectorPolynomialValue n a z) (vectorPolynomialValue n b z) =
      (∑ i ∈ Finset.range k, (metricPolynomial n a b).coeff i * z ^ i) +
      ∑ i ∈ Finset.Ico k (2 * n + 1), (metricPolynomial n a b).coeff i * z ^ i := by
  rw [← metricPolynomial_eval]
  conv_lhs => rw [(metricPolynomial n a b).as_sum_range' (2 * n + 1)
    (by have h := metricPolynomial_degree n a b; omega)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact (Finset.sum_range_add_sum_Ico _ hk).symm

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteSeriesAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the derivative series of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma shifted_derivative_sum (z : ℝ) (a b : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (z ^ (i + 1) • a i + z ^ i • b i)) =
      b 0 + (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (a (i - 1) + b i)) +
        z ^ (n + 1) • a n := by
  induction n with
  | zero => simp [add_comm]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    simp only [Nat.add_sub_cancel, smul_add]
    abel

lemma weighted_sum_split_zero (z : ℝ) (a : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), z ^ i • a i) =
      a 0 + ∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • a i := by
  rw [← Finset.sum_range_add_sum_Ico (fun i => z ^ i • a i) (by omega : 1 ≤ n + 1)]
  simp

lemma weighted_sum_split_endpoints (z : ℝ) (a : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 2), z ^ i • a i) =
      a 0 + (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • a i) + z ^ (n + 1) • a (n + 1) := by
  rw [Finset.sum_range_succ, weighted_sum_split_zero]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric polynomial coefficients of the finite periodic derivative ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_interior (dx : A) (U : ℕ → Family O E) {L i : ℕ}
    (hi : 0 < i) (hL : i < L) : g.xTangent dx U L i = xCoefficient dx U i := by
  simp only [xTangent, ne_of_gt hi, ne_of_lt hL, ite_false, if_false]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_pos (U : ℕ → Family O E) {i : ℕ} (hi : 0 < i) :
    g.yTangent U i = yCoefficient dy U i := by
  simp only [yTangent, ne_of_gt hi, ite_false, if_false]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xxPolynomial dx U L p t).coeff r = (g.xxCoefficient dx U r).val p t := by
  unfold xxPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.xTangent dx U L (r - i)).val p t)) =
      (xxQuadratic dx U r).val p t := by
    simp only [xxQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega),
      g.xTangent_interior dx U (by omega) (by omega)]
  rw [hs]
  simp only [xxCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.longitudinal.val p t)]
  ring

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xyPolynomial dx U L p t).coeff r = (g.xyCoefficient dx U r).val p t := by
  unfold xyPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (xyQuadratic dx dy U r).val p t := by
    simp only [xyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [xyCoefficient, Family.add_apply, Family.inner_apply]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.transverse.val p t)]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyPolynomial_coeff (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r ≤ L) (p : A) (t : Period) :
    (g.yyPolynomial U L p t).coeff r = (g.yyCoefficient U r).val p t := by
  unfold yyPolynomial
  rw [metricPolynomial_coeff_pos hL hr, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.yTangent U i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (yyQuadratic dy U r).val p t := by
    simp only [yyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.yTangent_pos U (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [yyCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((yCoefficient dy U r).val p t) (g.transverse.val p t)]
  ring

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coefficient families and exact remainder of the finite metric expansion. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metricCoefficientFamily_apply (n r : ℕ) (a b : ℕ → Family O E) (p : A) (t : Period) :
    (metricCoefficientFamily n r a b).val p t =
      (metricPolynomial n (fun i => (a i).val p t) (fun i => (b i).val p t)).coeff r := by
  simp only [metricCoefficientFamily, Family.sum_apply, metricPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · simp only [h, Family.inner_apply, Polynomial.coeff_monomial_same]
  · simp only [Polynomial.coeff_monomial, h, ite_false, if_false, Family.zero_apply]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jet-polynomial representations of every coefficient of the finite
pullback-metric remainder. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

lemma smooth_finiteMetric {O : Set LowJet} {X Y : ℕ → VectorExpression}
    (hX : ∀ i, (X i).SmoothCoeffs O) (hY : ∀ i, (Y i).SmoothCoeffs O) (L r : ℕ) :
    (finiteMetric L r X Y).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  apply Expression.smoothCoeffs_sumFinset
  intro j _
  split_ifs
  · exact VectorExpression.smoothCoeffs_dot (hX i) (hY j)
  · exact contDiffOn_const

lemma order_finiteMetric {X Y : ℕ → VectorExpression} {L N : ℕ} (hN : 2 ≤ N)
    (hX : ∀ i ≤ L, ∀ a, (X i a).order ≤ N)
    (hY : ∀ i ≤ L, ∀ a, (Y i a).order ≤ N) (r : ℕ) :
    (finiteMetric L r X Y).order ≤ N := by
  apply Expression.order_sumFinset_le _ _ _ hN
  intro i hi
  apply Expression.order_sumFinset_le _ _ _ hN
  intro j hj
  split_ifs
  · exact VectorExpression.order_dot_le hN
      (hX i (by simpa using Finset.mem_range.mp hi))
      (hY j (by simpa using Finset.mem_range.mp hj))
  · exact hN

lemma represents_finiteMetric {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {X Y : ℕ → VectorExpression} {A B : ℕ → Family S R4}
    (hX : ∀ i, VectorExpression.Represents G (X i) (A i))
    (hY : ∀ i, VectorExpression.Represents G (Y i) (B i)) (L r : ℕ) :
    Expression.Represents G (finiteMetric L r X Y) (metricCoefficientFamily L r A B) := by
  apply Expression.represents_sumFinset
  intro i _
  apply Expression.represents_sumFinset
  intro j _
  split_ifs
  · exact Expression.represents_dot (hX i) (hY j)
  · intro p _ t
    rfl

lemma smooth_xTangent {O : Set LowJet} (hO : IsOpen O) {X : VectorExpression}
    {U : ℕ → VectorExpression} (hX : X.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dx : Fin 2) (L i : ℕ) : (xTangent X dx U L i).SmoothCoeffs O := by
  unfold xTangent
  split_ifs
  · exact hX
  · intro a
    exact Expression.smoothCoeffs_slow hO dx (hU _ a)
  · exact smooth_xCoefficient hO hU dx i

lemma smooth_yTangent {O : Set LowJet} (hO : IsOpen O) {Y : VectorExpression}
    {U : ℕ → VectorExpression} (hY : Y.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dy : Fin 2) (i : ℕ) : (yTangent Y dy U i).SmoothCoeffs O := by
  unfold yTangent
  split_ifs
  · exact hY
  · exact smooth_yCoefficient hO hU dy i

lemma represents_xTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) {dy : Base} (g : Geometry (E := R4) S dy)
    {X : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i))
    (dx : Fin 2) (L i : ℕ) :
    VectorExpression.Represents G (xTangent X dx U L i) (g.xTangent (coordinateVector dx) W L i) := by
  unfold xTangent Geometry.xTangent
  split_ifs
  · exact hX
  · exact VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx
  · exact represents_xCoefficient hO hG hQ hUs hU dx i

lemma represents_yTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dy : Fin 2) (g : Geometry (E := R4) S (coordinateVector dy))
    {Y : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hY : VectorExpression.Represents G Y g.transverse)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i)) (i : ℕ) :
    VectorExpression.Represents G (yTangent Y dy U i) (g.yTangent W i) := by
  unfold yTangent Geometry.yTangent
  split_ifs
  · exact hY
  · exact represents_yCoefficient hO hG hQ hUs hU dy i

lemma order_xTangent {X : VectorExpression} {U : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2)
    (hU : ∀ j < L, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (xTangent X dx U L i a).order ≤ 2 * L + 1 := by
  unfold xTangent
  split_ifs with hi0 hiL
  · exact (hX a).trans (by omega)
  · have hprev := hU (i - 1) (by omega) a
    have hh := Expression.order_slow_le dx (U (i - 1) a)
    change ((U (i - 1) a).slow dx).order ≤ _
    omega
  · exact (order_xCoefficient (by omega) (by omega) hU dx a).trans (by omega)

lemma order_yTangent {Y : VectorExpression} {U : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hY : ∀ a, (Y a).order ≤ 2)
    (hU : ∀ j < L, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (yTangent Y dy U i a).order ≤ 2 * L + 1 := by
  unfold yTangent
  split_ifs with hi0
  · exact (hY a).trans (by omega)
  · exact (order_yCoefficient (by omega) hi hU dy a).trans (by omega)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFastRemainderBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite high-order metric tail has the required `z^L` gain after
fast evaluation, with a slow-scale loss independent of derivative order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion WeightedEstimates

theorem compact_scalar_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + e.order) B (lowJet G) →
      ∀ (U : Family S ℝ), Represents G e U →
        WeightedBound S z m (D / s ^ e.loss) (U.fastValue ℓ z) := by
  obtain ⟨D, hD, hd⟩ := compact_periodic_fast_bound S.isOpen hO hK hKO e he ℓ m B hB
  exact ⟨D, hD, fun G s z hz hzs hs1 hG hGK hb U hR =>
    hd G s z hz hzs hs1 hG hGK hb (fun p t => U.val p t) hR⟩

/-- This is the finite-tail estimate used for the pullback-metric error.
Every coefficient is an actual represented family; its derivatives are not
postulated as hypotheses. -/
theorem compact_tail_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ℕ → Expression) (hRs : ∀ r, (R r).SmoothCoeffs O) (L T N d : ℕ)
    (hN : ∀ r ∈ Finset.Ico L T, (R r).order ≤ N)
    (hd : ∀ r ∈ Finset.Ico L T, (R r).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (U : ℕ → Family S ℝ), (∀ r ∈ Finset.Ico L T, Represents G (R r) (U r)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L T, z ^ r * (U r).fastValue ℓ z p) := by
  classical
  have hex := fun r => compact_scalar_fast_bound (S := S) hO hK hKO (R r) (hRs r) ℓ m B hB
  choose C hC hc using hex
  refine ⟨∑ r ∈ Finset.Ico L T, C r, Finset.sum_nonneg (fun r _ => hC r), ?_⟩
  intro G s z hz hzs hs1 hG hGK hb U hrep
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico L T) :
      WeightedBound S z m (C r * z ^ L / s ^ d)
        (fun p => z ^ r • (U r).fastValue ℓ z p) := by
    have hh := hc r G s z hz hzs hs1 hG hGK
      (hb.mono_order (Nat.add_le_add_left (hN r hr) m)) (U r) (hrep r hr)
    have hh' : WeightedBound S z m (C r / s ^ d) ((U r).fastValue ℓ z) :=
      hh.mono_const (div_le_div_of_nonneg_left (hC r) (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (hd r hr)))
    have hmul := hh'.const_smul S.isOpen.uniqueDiffOn ((U r).fastValue_smooth ℓ z) (z ^ r)
    apply hmul.mono_const
    rw [abs_of_nonneg (pow_nonneg hz.le _)]
    calc
      z ^ r * (C r / s ^ d) ≤ z ^ L * (C r / s ^ d) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hz.le hz1 (Finset.mem_Ico.mp hr).1)
          (div_nonneg (hC r) (pow_nonneg hs.le _))
      _ = C r * z ^ L / s ^ d := by ring
  have hh := WeightedBound.finset_sum S.isOpen.uniqueDiffOn hz.le (Finset.Ico L T)
    (fun r => C r * z ^ L / s ^ d) (fun r p => z ^ r • (U r).fastValue ℓ z p)
    (fun r _ => (contDiffOn_const (c := z ^ r)).smul ((U r).fastValue_smooth ℓ z)) hterm
  have heq : (∑ r ∈ Finset.Ico L T, C r * z ^ L / s ^ d) =
      (∑ r ∈ Finset.Ico L T, C r) * z ^ L / s ^ d := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [heq] at hh
  simpa only [smul_eq_mul] using hh

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the actual finite pullback-metric tail. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

/-- A single finite algebraic loss bounds the true metric remainder, at every
weighted derivative order. This applies to each of xx, xy, and yy by choosing
the two tangent coefficient sequences. -/
theorem compact_finite_metric_tail {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : ℕ → VectorExpression) (hXs : ∀ i, (X i).SmoothCoeffs O)
    (hYs : ∀ i, (Y i).SmoothCoeffs O) (L N : ℕ) (hN : 2 ≤ N)
    (hX : ∀ i ≤ L, ∀ a, (X i a).order ≤ N)
    (hY : ∀ i ≤ L, ∀ a, (Y i a).order ≤ N) (ℓ : Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + N) B (lowJet G) →
      ∀ (A B : ℕ → Family S R4),
        (∀ i, VectorExpression.Represents G (X i) (A i)) →
        (∀ i, VectorExpression.Represents G (Y i) (B i)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L (2 * L + 1),
            z ^ r * (metricCoefficientFamily L r A B).fastValue ℓ z p) := by
  let R := fun r => finiteMetric L r X Y
  let d := (Finset.Ico L (2 * L + 1)).sup (fun r => (R r).loss)
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := Expression.compact_tail_bound (S := S) hO hK hKO R
    (fun r => smooth_finiteMetric hXs hYs L r) L (2 * L + 1) N d
    (fun r _ => order_finiteMetric hN hX hY r)
    (fun r hr => Finset.le_sup (f := fun r => (R r).loss) hr) ℓ m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb A B hA hB
  exact hb G s z hz hzs hs1 hG hGK hGb (fun r => metricCoefficientFamily L r A B)
    (fun r _ => represents_finiteMetric hA hB L r)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TangentMetricBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite-tail estimate to the actual two tangent expansions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

lemma smooth_tangentExpression {O : Set LowJet} (hO : IsOpen O)
    {X Y : VectorExpression} {R : ℕ → VectorExpression}
    (hX : X.SmoothCoeffs O) (hY : Y.SmoothCoeffs O) (hR : ∀ i, (R i).SmoothCoeffs O)
    (dx dy : Fin 2) (L : ℕ) (b : Bool) (i : ℕ) :
    (tangentExpression X Y R dx dy L b i).SmoothCoeffs O := by
  cases b
  · exact smooth_yTangent hO hY hR dy i
  · exact smooth_xTangent hO hX hR dx L i

lemma order_tangentExpression {X Y : VectorExpression} {R : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < L, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b : Bool) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (tangentExpression X Y R dx dy L b i a).order ≤ 2 * L + 1 := by
  cases b
  · exact order_yTangent hL hY hR dy hi a
  · exact order_xTangent hL hX hR dx hi a

lemma represents_tangentExpression {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dx dy : Fin 2)
    (g : Geometry (E := R4) S (coordinateVector dy))
    {X Y : VectorExpression} {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hY : VectorExpression.Represents G Y g.transverse)
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    (L : ℕ) (b : Bool) (i : ℕ) :
    VectorExpression.Represents G (tangentExpression X Y R dx dy L b i)
      (tangentFamily g U (coordinateVector dx) L b i) := by
  cases b
  · exact represents_yTangent hO hG hQ dy g hY hRs hR i
  · exact represents_xTangent hO hG hQ g hX hRs hR dx L i

/-- The two choices of tangent yield the xx, xy, and yy metric tails.
The exponent is fixed by the finite expression, independently of `m`. -/
theorem compact_tangent_metric_tail {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
    (L : ℕ) (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < L, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (2 * L + 1)) B (lowJet G) →
      ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4),
        VectorExpression.Represents G X g.longitudinal →
        VectorExpression.Represents G Y g.transverse →
        (∀ i, VectorExpression.Represents G (R i) (U i)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L (2 * L + 1), z ^ r *
            (metricCoefficientFamily L r (tangentFamily g U (coordinateVector dx) L b)
              (tangentFamily g U (coordinateVector dx) L c)).fastValue ℓ z p) := by
  obtain ⟨d, hd⟩ := compact_finite_metric_tail (S := S) hO hK hKO
    (tangentExpression X Y R dx dy L b) (tangentExpression X Y R dx dy L c)
    (smooth_tangentExpression hO hXs hYs hRs dx dy L b)
    (smooth_tangentExpression hO hXs hYs hRs dx dy L c) L (2 * L + 1) (by omega)
    (fun i hi a => order_tangentExpression hL hX hY hR dx dy b hi a)
    (fun i hi a => order_tangentExpression hL hX hY hR dx dy c hi a) ℓ
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb g U hXg hYg hrep
  have hQ : Set.MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  exact hb G s z hz hzs hs1 hG hGK hGb _ _
    (represents_tangentExpression hO hG hQ dx dy g hXg hYg hRs hrep L b)
    (represents_tangentExpression hO hG hQ dx dy g hXg hYg hRs hrep L c)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFiniteAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma finiteAnsatz_fderiv {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (U : ℕ → Family O E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hp : p ∈ O) (v : A) :
    fderiv ℝ (finiteAnsatz F U ℓ L z) p v = fderiv ℝ F p v +
      ∑ i ∈ Finset.range L, z ^ (i + 1) •
        (((U i).slow v).val p ((ℓ p / z : ℝ) : Period) +
          (ℓ v / z) • (U i).angle.val p ((ℓ p / z : ℝ) : Period)) := by
  have hd (i : ℕ) : DifferentiableAt ℝ ((U i).fastValue ℓ z) p :=
    (((U i).fastValue_smooth ℓ z).contDiffAt (O.isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hterm (i : ℕ) : DifferentiableAt ℝ
      (fun q => z ^ (i + 1) • (U i).fastValue ℓ z q) p := (hd i).const_smul _
  have hsum : DifferentiableAt ℝ
      (fun q => ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z q) p :=
    DifferentiableAt.fun_sum (fun i _ => hterm i)
  unfold finiteAnsatz
  rw [fderiv_fun_add ((hF.contDiffAt (O.isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hsum]
  rw [fderiv_fun_sum (fun i _ => hterm i)]
  simp only [add_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_fun_const_smul (hd i), smul_apply,
    Family.fastValue_fderiv _ _ _ hp]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicAnsatzMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the finite metric polynomial with derivatives of the actual map. -/

noncomputable section
open scoped BigOperators ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_value (dx : A) (U : ℕ → Family O E) (n : ℕ) (p : A) (t : Period) (z : ℝ) :
    vectorPolynomialValue (n + 1) (fun i => (g.xTangent dx U (n + 1) i).val p t) z =
      g.longitudinal.val p t +
        (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (xCoefficient dx U i).val p t) +
          z ^ (n + 1) • ((U n).slow dx).val p t := by
  rw [vectorPolynomialValue, weighted_sum_split_endpoints, g.xTangent_zero]
  have he : (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (g.xTangent dx U (n + 1) i).val p t) =
      ∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (xCoefficient dx U i).val p t := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hil⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) hil]
  rw [he]
  simp only [xTangent, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, if_false,
    ite_true, if_true, Nat.add_sub_cancel]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_value (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) (z : ℝ) :
    vectorPolynomialValue L (fun i => (g.yTangent U i).val p t) z =
      g.transverse.val p t + ∑ i ∈ Finset.range L, z ^ (i + 1) • ((U i).slow dy).val p t := by
  rw [vectorPolynomialValue, weighted_sum_split_zero, g.yTangent_zero]
  congr 1
  have he := Finset.sum_Ico_add' (fun i => z ^ i • (g.yTangent U i).val p t) 0 L 1
  simp only [zero_add, Nat.Ico_zero_eq_range] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i hi
  rw [g.yTangent_pos U (by omega)]
  simp only [yCoefficient, Nat.add_sub_cancel]

omit [FiniteDimensional ℝ E] in
lemma finiteAnsatz_x {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (U : ℕ → Family O E) (hinit : U 0 = g.initial)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hℓ : ℓ dx = 1)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (n : ℕ) (z : ℝ) (hz : z ≠ 0) {p : A} (hp : p ∈ O) :
    fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p dx =
      vectorPolynomialValue (n + 1)
        (fun i => (g.xTangent dx U (n + 1) i).val p ((ℓ p / z : ℝ) : Period)) z := by
  let t : Period := ((ℓ p / z : ℝ) : Period)
  have hs : (∑ i ∈ Finset.range (n + 1), z ^ (i + 1) •
      (((U i).slow dx).val p t + (ℓ dx / z) • (U i).angle.val p t)) =
      ∑ i ∈ Finset.range (n + 1),
        (z ^ (i + 1) • ((U i).slow dx).val p t + z ^ i • (U i).angle.val p t) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_add, smul_smul, hℓ]
    congr 1
    congr 1
    field_simp
    ring
  rw [finiteAnsatz_fderiv hF U ℓ _ _ hp, hs,
    shifted_derivative_sum z (fun i => ((U i).slow dx).val p t)
      (fun i => (U i).angle.val p t) n, g.xTangent_value]
  have hlead : fderiv ℝ F p dx + (U 0).angle.val p t = g.longitudinal.val p t := by
    rw [hinit, g.initial_angle, hX p hp]
    simp only [Family.sub_apply, Family.vectorMean_apply, longitudinal,
      Family.add_apply, Family.constant_apply _ _ hp]
    abel
  simp only [← add_assoc, hlead]
  rfl

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_y {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (U : ℕ → Family O E) (ℓ : A →L[ℝ] ℝ) (hℓ : ℓ dy = 0)
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p) (L : ℕ) (z : ℝ) {p : A} (hp : p ∈ O) :
    fderiv ℝ (finiteAnsatz F U ℓ L z) p dy =
      vectorPolynomialValue L
        (fun i => (g.yTangent U i).val p ((ℓ p / z : ℝ) : Period)) z := by
  rw [finiteAnsatz_fderiv hF U ℓ _ _ hp, g.yTangent_value, hY p hp]
  simp only [hℓ, zero_div, zero_smul, add_zero, transverse, Family.constant_apply _ _ hp]

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFiniteMetricIdentity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite metric expansion of the actual oscillatory map. -/

noncomputable section
open scoped BigOperators ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma polynomial_zero_coefficients (dx : A) (U : ℕ → Family O E) (L : ℕ)
    {p : A} (hpO : p ∈ O) (t : Period) :
    (g.xxRemainder dx U L 0).val p t = inner ℝ (g.X₀ p) (g.X₀ p) + g.q p ∧
    (g.xyRemainder dx U L 0).val p t = inner ℝ (g.X₀ p) (g.Y p) ∧
    (g.yyRemainder U L 0).val p t = inner ℝ (g.Y p) (g.Y p) := by
  have hp := g.perpX₀ p hpO _ (g.V_mem p hpO t)
  have hy := g.perpY p hpO _ (g.V_mem p hpO t)
  have hp' : inner ℝ (g.V.val p t) (g.X₀ p) = 0 := by
    rw [real_inner_comm]
    exact hp
  have hy' : inner ℝ (g.V.val p t) (g.Y p) = 0 := by
    rw [real_inner_comm]
    exact hy
  simp only [xxRemainder, xyRemainder, yyRemainder, metricCoefficientFamily_apply,
    metricPolynomial_coeff (Nat.zero_le L), Finset.sum_range_one, Nat.sub_zero,
    xTangent_zero, yTangent_zero, longitudinal, transverse, Family.add_apply,
    Family.constant_apply _ _ hpO, inner_add_left, inner_add_right, hp, hp', hy', g.circle p hpO t, add_zero,
    zero_add]
  trivial

omit [FiniteDimensional ℝ E] in
/-- The exact metric identity, before replacing low coefficients by their means. -/
theorem finite_metric_identity {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (U : ℕ → Family O E) (hinit : U 0 = g.initial)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hℓx : ℓ dx = 1) (hℓy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p)
    (n : ℕ) (z : ℝ) (hz : z ≠ 0) {p : A} (hpO : p ∈ O) :
    let f := finiteAnsatz F U ℓ (n + 1) z
    let t : Period := ((ℓ p / z : ℝ) : Period)
    let L := n + 1
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx) =
      (∑ r ∈ Finset.range L, (g.xxRemainder dx U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.xxRemainder dx U L r).val p t * z ^ r ∧
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy) =
      (∑ r ∈ Finset.range L, (g.xyRemainder dx U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.xyRemainder dx U L r).val p t * z ^ r ∧
    inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy) =
      (∑ r ∈ Finset.range L, (g.yyRemainder U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.yyRemainder U L r).val p t * z ^ r := by
  dsimp only
  rw [g.finiteAnsatz_x hF U hinit ℓ dx hℓx hX n z hz hpO,
    g.finiteAnsatz_y hF U ℓ hℓy hY (n + 1) z hpO]
  simp only [xxRemainder, xyRemainder, yyRemainder, metricCoefficientFamily_apply]
  exact ⟨metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z,
    metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z,
    metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalMetricExpansionWitness
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite metric expansion for a specified cancelling coefficient
sequence, allowing the quantitative estimates to use the same witness. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (weighted_sum_split_zero)

private lemma split_constant (n : ℕ) (c e : ℕ → ℝ) (q z : ℝ)
    (hzero : c 0 = q) (h : ∀ r, 0 < r → r < n + 1 → c r = e r) :
    (∑ r ∈ Finset.range (n + 1), c r * z ^ r) =
      q + ∑ r ∈ Finset.Ico 1 (n + 1), e r * z ^ r := by
  have hs := weighted_sum_split_zero z c n
  simp only [smul_eq_mul, mul_comm] at hs
  rw [hs, hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hr, hrn⟩ := Finset.mem_Ico.mp hr
  rw [h r (by omega) hrn]

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {O : TopologicalSpace.Opens A} {dy : A}

namespace Geometry

omit [CompleteSpace E] in
lemma angle_independent_of_cancellation (g : Geometry (E := E) O dy)
    (dx : A) (U : ℕ → Family O E) (n : ℕ)
    (hy₁ : (g.yyCoefficient U 1).fluct = 0)
    (hc : ∀ r, 1 ≤ r → r ≤ n →
      (g.xxCoefficient dx U r).fluct = 0 ∧
      (g.xyCoefficient dx U r).fluct = 0 ∧ (g.yyCoefficient U (r + 1)).fluct = 0)
    {r : ℕ} (hr : 0 < r) (hrn : r < n + 1) (p : A) (t : Period) :
    (g.xxRemainder dx U (n + 1) r).val p t = average ((g.xxCoefficient dx U r).val p) ∧
    (g.xyRemainder dx U (n + 1) r).val p t = average ((g.xyCoefficient dx U r).val p) ∧
    (g.yyRemainder U (n + 1) r).val p t = average ((g.yyCoefficient U r).val p) := by
  obtain ⟨hx, hxy, _⟩ := hc r hr (by omega)
  have hy : (g.yyCoefficient U r).fluct = 0 := by
    by_cases he : r = 1
    · simpa only [he] using hy₁
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using
        (hc (r - 1) (by omega) (by omega)).2.2
  have mean_eq (f : Family O ℝ) (hf : f.fluct = 0) : f.val p t = average (f.val p) := by
    have ht := congrArg (fun w : Family O ℝ => w.val p t) hf
    simp only [Family.fluct_apply, fluctuation, Family.zero_apply] at ht
    exact sub_eq_zero.mp ht
  change (metricCoefficientFamily (n + 1) r _ _).val p t = _ ∧
    (metricCoefficientFamily (n + 1) r _ _).val p t = _ ∧
    (metricCoefficientFamily (n + 1) r _ _).val p t = _
  simp only [metricCoefficientFamily_apply]
  exact ⟨(g.xxPolynomial_coeff dx U hr hrn p t).trans (mean_eq _ hx),
    (g.xyPolynomial_coeff dx U hr hrn p t).trans (mean_eq _ hxy),
    (g.yyPolynomial_coeff U hr (by omega) p t).trans (mean_eq _ hy)⟩

/-- The exact expansion retains a given coefficient witness, rather than
choosing a new sequence without its proved estimates. -/
theorem finite_expansion_of_cancellation (g : Geometry (E := E) O dy)
    {F : A → E} (hF : ContDiffOn ℝ ∞ F O) (U : ℕ → Family O E)
    (hinit : U 0 = g.initial) (n : ℕ) (dx : A)
    (hy₁ : (g.yyCoefficient U 1).fluct = 0)
    (hc : ∀ r, 1 ≤ r → r ≤ n →
      (g.xxCoefficient dx U r).fluct = 0 ∧
      (g.xyCoefficient dx U r).fluct = 0 ∧ (g.yyCoefficient U (r + 1)).fluct = 0)
    (ℓ : A →L[ℝ] ℝ) (hℓx : ℓ dx = 1) (hℓy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p)
    (z : ℝ) (hz : z ≠ 0) {p : A} (hp : p ∈ O) :
    let f := finiteAnsatz F U ℓ (n + 1) z
    let t : Period := ((ℓ p / z : ℝ) : Period)
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx) =
      (inner ℝ (g.X₀ p) (g.X₀ p) + g.q p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient dx U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.xxRemainder dx U (n + 1) r).val p t * z ^ r) ∧
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy) =
      inner ℝ (g.X₀ p) (g.Y p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient dx U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.xyRemainder dx U (n + 1) r).val p t * z ^ r) ∧
    inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy) =
      inner ℝ (g.Y p) (g.Y p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.yyRemainder U (n + 1) r).val p t * z ^ r) := by
  dsimp only
  let t : Period := ((ℓ p / z : ℝ) : Period)
  obtain ⟨hxx, hxy, hyy⟩ := g.finite_metric_identity hF U hinit ℓ dx hℓx hℓy hX hY n z hz hp
  obtain ⟨hxx₀, hxy₀, hyy₀⟩ := g.polynomial_zero_coefficients dx U (n + 1) hp t
  have hcoeff := fun (r : ℕ) (hr : 0 < r) (hn : r < n + 1) =>
    g.angle_independent_of_cancellation dx U n hy₁ hc hr hn p t
  rw [split_constant n _ _ _ z hxx₀ (fun r hr hn => (hcoeff r hr hn).1)] at hxx
  rw [split_constant n _ _ _ z hxy₀ (fun r hr hn => (hcoeff r hr hn).2.1)] at hxy
  rw [split_constant n _ _ _ z hyy₀ (fun r hr hn => (hcoeff r hr hn).2.2)] at hyy
  exact ⟨hxx, hxy, hyy⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuantitativeMetricExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pullback metric, after subtracting its finite mean expansion,
has the fast-scale remainder bound used by the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

namespace MetricPolynomial

/-- In each metric component, the error of the actual finite oscillatory map
relative to its mean expansion is `O_z(z^(n+1) / s^d)`. The fixed loss is
chosen before the slow map, both scales, or the derivative order. -/
theorem compact_metric_error_oai {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
    (n : ℕ) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < n + 1, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector dx) = 1) (hℓy : ℓ (coordinateVector dy) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
      ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4)
        (F : Base → R4),
        VectorExpression.Represents G X g.longitudinal →
        VectorExpression.Represents G Y g.transverse →
        (∀ i, VectorExpression.Represents G (R i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) →
        ContDiffOn ℝ ∞ F S →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dx) = g.X₀ p + average (g.V.val p)) →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dy) = g.Y p) →
        WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
          (fun p => inner ℝ
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) b))
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) c)) -
            meanMetric g (coordinateVector dx) U n b c z p) := by
  obtain ⟨d, hd⟩ := compact_tangent_metric_tail hO hK hKO X Y R hXs hYs hRs
    (n + 1) (by omega) hX hY hR dx dy (b || c) (b && c) ℓ
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb g U F hXg hYg hrep hinit hy hc hF hDX hDY
  have htail := hb G s z hz hzs hs1 hG hGK hGb g U hXg hYg hrep
  apply htail.congr
  intro p hp
  obtain ⟨hxx, hxy, hyy⟩ := g.finite_expansion_of_cancellation hF U hinit n
    (coordinateVector dx) hy hc ℓ hℓx hℓy hDX hDY z hz.ne' hp
  cases b <;> cases c
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.yyRemainder U (n + 1) r).val p _
    rw [hyy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    rw [real_inner_comm]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xyRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xyRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xxRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxx]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error_oai := @OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error_oai
