-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:09.333952+00:00
-- url     : https://prove2.me/submissions/40bc9bb6-0e7a-4c93-9315-b20d6f23e268

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_slow_step

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance planeReadSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_add {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T+S) := by
  intro i
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T+S))
  rw [A.bundleLocalize_add]
  exact (hbT i).add uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasOuterDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded open coordinate domains containing every outer cutoff support. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_outer_domains :
    ∃ (U : A.centers → Set JetPolynomial.Base) (K : A.centers → Compacts JetPolynomial.Base),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ K i) ∧
      (∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i) ∧
      (∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) := by
  classical
  have hc (i : A.centers) : IsCompact ((chart (i : M)) '' tsupport (A.outer i)) :=
    (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.outer_support i))
  choose U hU hKU hUc _ using fun i => CollarVelocity.compact_open_thickening
    (hc i) isOpen_univ (subset_univ _)
  refine ⟨U,fun i => ⟨closure (U i),hUc i⟩,hU,fun _ => subset_closure,?_,hKU⟩
  intro i x hx
  obtain ⟨p,hp,rfl⟩ := hx
  apply hKU i
  refine ⟨p,subset_tsupport (A.outer i) ?_,rfl⟩
  change A.outer i p ≠ 0
  rw [A.outer_one i p hp]
  exact one_ne_zero

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perturbation operators and their actual first variations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {n : ℕ}

lemma eval_smooth {O : Set LowJet} {U : Set Base} {P : Fin n → Expression}
    (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O) :
    ContDiffOn ℝ ∞ (eval P ε G) (U ×ˢ Set.univ) := by
  exact ContDiffOn.sum (fun l _ => contDiffOn_const.mul ((P l).eval_smooth hG hQ (hP l)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialValueBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform evaluation bounds for the polynomial part of the actual mean
metric. The loss is fixed by P, before any accuracy order is chosen. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinatePolynomialValue_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinatePolynomialValue P ε G 0) := by
  apply contDiff_pi.mpr
  intro k
  have hs : ContDiff ℝ ∞ (fun p : Base => eval (P k) ε G (p,0)) := by
    have he : ContDiff ℝ ∞ (eval (P k) ε G) := contDiffOn_univ.mp (by
      simpa only [Set.univ_prod_univ] using
        (eval_smooth (U := Set.univ) (hP k) ε hG (fun _ _ => Set.mem_univ _)))
    exact he.comp (contDiff_id.prodMk contDiff_const)
  change ContDiff ℝ ∞ ((fun p : Base => eval (P k) ε G (p,0)) ∘ planeCoordinateIsometry.symm)
  exact hs.comp planeCoordinateIsometry.symm.contDiff

theorem coordinatePolynomialValue_bound {n : ℕ} {Q : Set LowJet}
    (hQ : IsCompact Q) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set Base), IsOpen U →
      ∀ {G : Base → Space}, ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U Q →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m
        (D * ε / s ^ tensorLoss P) (coordinatePolynomialValue P ε G 0) := by
  classical
  choose D hD hd using fun k l => Expression.compact_phase_bound isOpen_univ hQ
    (Set.subset_univ _) (P k l) (hP k l) m B 1 hB le_rfl
  let E : ℝ := ∑ k, ∑ l, D k l
  have hE : 0 ≤ E := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hD k l
  refine ⟨E,hE,?_⟩
  intro U hU G hG hGQ s ε hs hs1 hε hε1 hGb
  have ho (k : Fin 3) (l : Fin n) : (P k l).order ≤ tensorOrder P :=
    (Finset.le_sup (f := fun l => (P k l).order) (Finset.mem_univ l)).trans
      (Finset.le_sup (f := fun k => order (P k)) (Finset.mem_univ k))
  have hl (k : Fin 3) (l : Fin n) : (P k l).loss ≤ tensorLoss P := by
    have h₁ := Finset.le_sup (f := fun l => (P k l).loss + 6) (Finset.mem_univ l)
    change (P k l).loss + 6 ≤ loss (P k) at h₁
    have h₂ := Finset.le_sup (f := fun k => loss (P k)) (Finset.mem_univ k)
    change _ ≤ tensorLoss P at h₂
    exact (by omega : (P k l).loss ≤ loss (P k)).trans h₂
  have hsmooth (k : Fin 3) (l : Fin n) :
      ContDiff ℝ ∞ (fun p : Base => (P k l).eval G (p,0)) := by
    have hh := (P k l).eval_smooth (S := Set.univ) hG
      (fun _ _ => Set.mem_univ _) (hP k l)
    have hh' : ContDiff ℝ ∞ ((P k l).eval G) :=
      contDiffOn_univ.mp (by simpa only [Set.univ_prod_univ] using hh)
    exact hh'.comp (contDiff_id.prodMk contDiff_const)
  have hb (k : Fin 3) (l : Fin n) : WeightedBound U s m
      (D k l * ε / s ^ tensorLoss P) (fun x => ε^(l.val+1) * (P k l).eval G (x,0)) := by
    have he := hd k l U hU G (fun _ => 0) s s hs le_rfl hs1 hG contDiffOn_const hGQ
      (fun _ _ => by constructor <;> norm_num)
      (hGb.mono_order (Nat.add_le_add_left (ho k l) m))
      ((weightedBound_zero U s m (F := ℝ)).mono_const zero_le_one)
    have he' := he.const_smul hU.uniqueDiffOn (hsmooth k l).contDiffOn (ε^(l.val+1))
    apply (he'.congr (fun _ _ => by simp only [smul_eq_mul])).mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have hp : ε^(l.val+1) ≤ ε := by
      simpa only [pow_one] using
        pow_le_pow_of_le_one hε hε1 (by omega : 1 ≤ l.val+1)
    calc
      _ ≤ ε * (D k l / s^(P k l).loss) := mul_le_mul_of_nonneg_right hp
        (div_nonneg (hD k l) (pow_nonneg hs.le _))
      _ ≤ ε * (D k l / s^tensorLoss P) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (hD k l) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (hl k l))) hε
      _ = _ := by ring
  have hsum (k : Fin 3) : WeightedBound U s m
      ((∑ l, D k l) * ε / s^tensorLoss P) (fun x => eval (P k) ε G (x,0)) := by
    have hh := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
      (fun l => D k l * ε / s^tensorLoss P)
      (fun l x => ε^(l.val+1) * (P k l).eval G (x,0))
      (fun l _ => ((hsmooth k l).const_smul (ε^(l.val+1))).contDiffOn)
      (fun l _ => hb k l)
    simpa only [eval,← Finset.sum_mul,← Finset.sum_div] using hh
  have hsource : WeightedBound U s m (E*ε/s^tensorLoss P)
      (fun x k => eval (P k) ε G (x,0)) := by
    apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · intro k
      exact (ContDiff.sum (fun l _ => (hsmooth k l).const_smul (ε^(l.val+1)))).contDiffOn
    · intro k
      apply (hsum k).mono_const
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hD k l)
            (Finset.mem_univ k)) hε) (pow_nonneg hs.le _)
  have hsourceSmooth : ContDiff ℝ ∞ (fun x k => eval (P k) ε G (x,0)) := by
    apply contDiff_pi.mpr
    intro k
    exact ContDiff.sum (fun l _ => (hsmooth k l).const_smul (ε^(l.val+1)))
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU hsourceSmooth hsource

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualSmul
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
local instance polynomialMetricSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma atlasPolynomialValue_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialValue P ε G x)) :=
  A.tensorPlaneRestore_smooth (fun i => coordinatePolynomialValue_smooth (hP i)
    (A.jetChartMap_smooth i hG) ε)

lemma atlasPolynomialMetric_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialMetric P ε G x)) :=
  (A.inducedTensor_smooth hG).add_section (A.atlasPolynomialValue_smooth hP hG ε)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialValueBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberSpace
local instance polynomialValueDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberSpace
local instance polynomialValueDualSmul_r1962b4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberNormed
local instance polynomialValueSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialValueSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

/-- Fixed local low-jet bounds give a global bound on the actual restored
polynomial value. Its scale loss is the maximum of the chartwise losses. -/
theorem atlas_polynomial_value_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ i, WeightedEstimates.WeightedBound (U i) s (m + tensorOrder (P i)) (B i)
        (lowJet (A.jetChartMap i G))) →
      A.TensorWeightedBound s m
        (D * ε / s ^ (Finset.univ.sup fun i : A.centers => tensorLoss (P i)))
        (A.atlasPolynomialValue P ε G) := by
  classical
  choose K χ hχU hχone using fun i => A.polynomial_outer_cutoff i (hU i) (houter i)
  choose C hC hc using fun i => coordinatePolynomialValue_bound (hQ i) (P i) (hP i)
    m (B i) (hB i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let N : A.centers → ℝ := fun i => supportedWeightedSeminorm (K i) 1 m (χ i)
  have hN (i) : 0 ≤ N i := apply_nonneg _ _
  let E : A.centers → ℝ := fun i => 2 ^ m * N i * C i
  have hE (i) : 0 ≤ E i := mul_nonneg (mul_nonneg (by positivity) (hN i)) (hC i)
  let E₀ : ℝ := ∑ i, E i
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun i _ => hE i)
  let loss : ℕ := Finset.univ.sup fun i : A.centers => tensorLoss (P i)
  refine ⟨D * E₀,mul_nonneg hD hE₀,?_⟩
  intro G hG hGQ s ε hs hs1 hε hε1 hb
  let f : A.centers → SmallModes.Base → Tensor :=
    fun i => coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0
  let ψ : A.centers → SmallModes.Base → ℝ :=
    fun i => (χ i) ∘ planeCoordinateIsometry.symm
  let g : A.centers → SmallModes.Base → Tensor := fun i x => ψ i x • f i x
  have hf (i) : ContDiff ℝ ∞ (f i) :=
    coordinatePolynomialValue_smooth (hP i) (A.jetChartMap_smooth i hG) ε
  have hψ (i) : ContDiff ℝ ∞ (ψ i) := (χ i).contDiff.comp planeCoordinateIsometry.symm.contDiff
  have hg (i) : ContDiff ℝ ∞ (g i) := (hψ i).smul (hf i)
  have hψsp (i) : tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' U i := by
    apply (show tsupport (ψ i) ⊆
      planeCoordinateIsometry.symm ⁻¹' tsupport (χ i) from ?_).trans (preimage_mono (hχU i))
    apply closure_minimal _ ((isClosed_tsupport (χ i)).preimage
      planeCoordinateIsometry.symm.continuous)
    intro x hx
    exact subset_tsupport (χ i) hx
  have hψb (i) : WeightedEstimates.WeightedBound univ s m (N i) (ψ i) :=
    weightedBound_comp_isometry planeCoordinateIsometry.symm (χ i).contDiff
      ((weightedBound_of_supportedSeminorm (1 : ℝ≥0) m (χ i)).shrink_scale hs.le hs1)
  have hgb (i) : WeightedEstimates.WeightedBound univ s m (E i * ε / s ^ tensorLoss (P i)) (g i) := by
    let V := planeCoordinateIsometry.symm ⁻¹' U i
    have hV : IsOpen V := (hU i).preimage planeCoordinateIsometry.symm.continuous
    have hlocal := (hψb i).restrict_open hV
    have hpoly := hc i (U i) (hU i) (A.jetChartMap_smooth i hG) (hGQ i)
      s ε hs hs1 hε hε1 (hb i)
    have hprod := hlocal.smul_real hV.uniqueDiffOn hs.le (hN i)
      (div_nonneg (mul_nonneg (hC i) hε) (pow_nonneg hs.le _))
      (hψ i).contDiffOn (hf i).contDiffOn hpoly
    have heq : 2 ^ m * N i * (C i * ε / s ^ tensorLoss (P i)) =
        E i * ε / s ^ tensorLoss (P i) := by dsimp [E] <;> ring
    rw [heq] at hprod
    exact hprod.extend_support hV
      ((tsupport_smul_subset_left (ψ i) (f i)).trans (hψsp i))
      (div_nonneg (mul_nonneg (hE i) hε) (pow_nonneg hs.le _))
  have hglobal (i) : WeightedEstimates.WeightedBound univ s m (E₀ * ε / s ^ loss) (g i) := by
    apply (hgb i).mono_const
    have hEi : E i ≤ E₀ := Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)
    calc
      E i * ε / s ^ tensorLoss (P i) ≤ E₀ * ε / s ^ tensorLoss (P i) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hEi hε) (pow_nonneg hs.le _)
      _ ≤ E₀ * ε / s ^ loss := div_le_div_of_nonneg_left (mul_nonneg hE₀ hε)
        (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1
          (Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)))
  have hout := hd g s (E₀ * ε / s ^ loss) hs hs1
    (div_nonneg (mul_nonneg hE₀ hε) (pow_nonneg hs.le _)) hg hglobal
  have heq : A.tensorPlaneRestore g = A.atlasPolynomialValue P ε G := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ tsupport (A.outer i)
    · have hχp := hχone i p hp
      change A.outer i p • (A.tensorTriv i).symmL ℝ p
          (fiberFromThree ((χ i) (planeCoordinateIsometry.symm
            (planeCoordinateIsometry (chart (i : M) p))) • f i
              (planeCoordinateIsometry (chart (i : M) p)))) = _
      simp only [LinearIsometryEquiv.symm_apply_apply,hχp,one_smul]
      rfl
    · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [bundleRestore,hz,zero_smul]
  rw [heq] at hout
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [loss]
  ring


/-- One profile controls every derivative order, before the actual map and
scales are chosen. -/
theorem atlas_polynomial_value_bounds {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (B : A.centers → ℕ → ℝ) (hB : ∀ i m, 1 ≤ B i m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ i m, WeightedEstimates.WeightedBound (U i) s (m + tensorOrder (P i)) (B i m)
        (lowJet (A.jetChartMap i G))) →
      ∀ m, A.TensorWeightedBound s m
        (D m * ε / s ^ (Finset.univ.sup fun i : A.centers => tensorLoss (P i)))
        (A.atlasPolynomialValue P ε G) := by
  choose D hD hb using fun m => A.atlas_polynomial_value_bound P hP U hU houter Q hQ
    m (fun i => B i m) (fun i => hB i m)
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s ε hs hs1 hε hε1 hjet m
  exact hb m G hG hGQ s ε hs hs1 hε hε1 (fun i => hjet i m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberNormed
local instance initialSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    inducedTensor (a • F) = a^2 • inducedTensor F := by
  funext p
  ext v w
  have hd : (mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) =
      a • (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) :=
    const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) a
  change inner ℝ ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) v)
    ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) w) =
    a^2*inner ℝ (mfderiv planeModel spaceModel F p v) (mfderiv planeModel spaceModel F p w)
  have hv := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from v)) hd
  have hw := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from w)) hd
  change (mfderiv planeModel spaceModel (a • F) p v : Space) =
    a • (mfderiv planeModel spaceModel F p v : Space) at hv
  change (mfderiv planeModel spaceModel (a • F) p w : Space) =
    a • (mfderiv planeModel spaceModel F p w : Space) at hw
  calc
    _ = inner ℝ (a • (mfderiv planeModel spaceModel F p v : Space))
        (a • (mfderiv planeModel spaceModel F p w : Space)) :=
      congrArg₂ (fun x y : Space => inner ℝ x y) hv hw
    _ = _ := by rw [real_inner_smul_left,real_inner_smul_right]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitiveMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized mean identities for the global primitive iteration.
The residual is always that of the actual restored polynomial metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualSmul
variable (A : SmoothingAtlas M) {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberSpace
local instance atlasPrimitiveSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasPrimitiveSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma normalizedPolynomialDefect_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {ε δ : ℝ}
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.normalizedPolynomialDefect P ε δ γ G x)) :=
  (((hγ.sub_section (A.atlasPolynomialMetric_smooth hP hG ε)).const_smul_section).sub_section hγ)

omit [CompactSpace M] in
lemma normalizedPolynomialDefect_seed
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {δ : ℝ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) :
    A.normalizedPolynomialDefect P ε δ (inducedTensor F) (Real.sqrt (1-δ^2) • F) =
      (-(δ^2)⁻¹) • A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) := by
  unfold normalizedPolynomialDefect atlasPolynomialMetric
  rw [inducedTensor_const_smul hF,Real.sq_sqrt (sub_nonneg.mpr hδ1)]
  funext x
  ext v w
  change (δ^2)⁻¹*(inducedTensor F x v w-
    ((1-δ^2)*inducedTensor F x v w+
      A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) x v w))-inducedTensor F x v w =
        -(δ^2)⁻¹*A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) x v w
  field_simp
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetCompactRange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FixedOrderThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each fixed order, all analytic smallness conditions and the
finite derivative budget hold below one positive scale threshold. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ClosedSurfaceR4.ExactCorrection

lemma positive_power_threshold (c p b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε → c*t^p < b := by
  have hf : ContinuousAt (fun t : ℝ => c*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), c*t^p < b :=
    hf.eventually (gt_mem_nhds (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hb))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1,lt_min hε zero_lt_one,min_le_right _ _,?_⟩
  intro t ht hsmall
  apply heε
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hsmall.trans_le (min_le_left ε 1)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitialInputBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite initial input estimates for the scalar-contracted map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialBoundFiberNormed_r1962b4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r1962b4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_r1962b4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_r1962b4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

namespace SmoothingAtlas
local instance initialBoundFiberNormed_r1962b4_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r1962b4_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_r1962b4_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_r1962b4_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance initialBoundSectionNormed_r1962b4_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r1962b4_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

lemma shiftedBound_smul_of_abs_le_one {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C a : ℝ} {q m : ℕ}
    (_hs : 0 ≤ s) (hC : 0 ≤ C) (ha : |a| ≤ 1)
    (hb : A.ShiftedBound q m s C F) : A.ShiftedBound q m s C (a • F) := by
  intro i j hj x
  have hf := localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF
  change s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) (a • F)) x‖ ≤ C
  rw [localize_smul,iteratedFDeriv_const_smul_apply (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  calc
    _ = |a| * (s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) F) x‖) := by ring
    _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hb i j hj x) (abs_nonneg a)
    _ ≤ C := by nlinarith

omit [CompactSpace M] in
lemma shifted_zero_to_weighted {F : M → Space} {P : ℝ} {q : ℕ}
    (hb : A.ShiftedBound q 0 1 P F) : A.WeightedBound 1 q P F := by
  intro i j hj x _
  have hh := hb i j (by omega) x
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveSlowScales
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slow scales in the high-accuracy primitive realization.
These choices precede every accuracy order in its mean iteration. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma amplitudeExponent_pos (j : ℕ) : 0 < amplitudeExponent j := by
  unfold amplitudeExponent
  positivity

lemma amplitudeExponent_zero : amplitudeExponent 0 = 1/4 := by
  simp [amplitudeExponent]

lemma amplitudeExponent_succ (j : ℕ) :
    amplitudeExponent (j+1) = (6/5)*amplitudeExponent j := by
  simp only [amplitudeExponent,pow_succ]
  ring

lemma amplitudeExponent_lower (j : ℕ) : 1/4 ≤ amplitudeExponent j := by
  induction j with
  | zero => rw [amplitudeExponent_zero]
  | succ j ih => rw [amplitudeExponent_succ]; linarith

/-- A finite number of amplitude improvements achieves any prescribed finite
metric order. No derivative count enters the later accuracy choices. -/
lemma exists_amplitude_steps (R N : ℕ) :
    ∃ steps : ℕ, 1 ≤ steps ∧ (N : ℝ)+R+1 < 2*amplitudeExponent steps := by
  obtain ⟨j,hj⟩ := exists_nat_gt (10*((N : ℝ)+R+1))
  have hpow : 1+(j : ℝ)/5 ≤ (6/5 : ℝ)^j := by
    first | (convert one_add_mul_le_pow (a := (1/5 : ℝ)) (by norm_num) j using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((one_add_mul_le_pow (a := (1/5 : ℝ)) (by norm_num) j).trans (le_of_eq (by ring)))
  refine ⟨j+1,by omega,?_⟩
  rw [amplitudeExponent_succ]
  have hp : 0 < (6/5 : ℝ)^j := by positivity
  dsimp [amplitudeExponent]
  nlinarith

/-- The loss powers determine one slow exponent before choosing the finite
substitution accuracies in the primitive realization argument. -/
theorem exists_slow_exponent (R N L : ℕ) (hL : N+R < L) (p p₁ : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ σ*(p₁+2) < 1 ∧ σ*p < 1/2 ∧
      σ < 1/16 ∧ (L : ℝ)-R-σ*p₁ > N := by
  have hgap : 0 < (L : ℝ)-R-N := by
    have hh : (N : ℝ)+R < L := by exact_mod_cast hL
    linarith
  obtain ⟨η₁,hη₁,_,hb₁⟩ := ExactCorrection.positive_power_threshold (p₁+2) 1 1
    zero_lt_one zero_lt_one
  obtain ⟨η₂,hη₂,_,hb₂⟩ := ExactCorrection.positive_power_threshold p 1 (1/2)
    zero_lt_one (by norm_num)
  obtain ⟨η₃,hη₃,_,hb₃⟩ := ExactCorrection.positive_power_threshold p₁ 1
    ((L : ℝ)-R-N) zero_lt_one hgap
  let η := min (1/32) (min η₁ (min η₂ η₃))
  have hη : 0 < η := lt_min (by norm_num) (lt_min hη₁ (lt_min hη₂ hη₃))
  let σ := η/2
  have hσ : 0 < σ := half_pos hη
  have hση : σ < η := half_lt_self hη
  have hσ32 : σ < 1/32 := hση.trans_le (min_le_left _ _)
  have hσ₁ : σ < η₁ := hση.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hσ₂ : σ < η₂ := hση.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσ₃ : σ < η₃ := hση.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h₁ := hb₁ σ hσ hσ₁
  have h₂ := hb₂ σ hσ hσ₂
  have h₃ := hb₃ σ hσ hσ₃
  simp only [Real.rpow_one] at h₁ h₂ h₃
  refine ⟨σ,hσ,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma scaleExponent_bounds {σ : ℝ} (hσ : 0 < σ) {steps j : ℕ}
    (hs : 1 ≤ steps) (hj : j ≤ steps) :
    0 ≤ scaleExponent σ steps j ∧ scaleExponent σ steps j ≤ σ := by
  have hs' : 0 < (steps : ℝ) := by exact_mod_cast (by omega : 0 < steps)
  have hj' : (j : ℝ) ≤ steps := by exact_mod_cast hj
  unfold scaleExponent
  constructor
  · positivity
  · apply (div_le_iff₀ hs').mpr
    nlinarith

lemma scaleExponent_step {σ : ℝ} {steps j : ℕ} :
    scaleExponent σ steps (j+1)-scaleExponent σ steps j = σ/(steps : ℝ) := by
  simp only [scaleExponent,Nat.cast_add,Nat.cast_one]
  ring

/-- Both the normalized cubic remainder and the C3 displacement decay at
every stage of the finite slow iteration. -/
theorem slow_step_positive_powers {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ < 1/16)
    {steps j : ℕ} (hs : 1 ≤ steps) (hj : j < steps) :
    0 < 3*amplitudeExponent j-scaleExponent σ steps (j+1)-2*amplitudeExponent (j+1) ∧
    0 < amplitudeExponent j-2*scaleExponent σ steps (j+1) ∧
    0 < min (σ/(steps : ℝ)) (1/2) := by
  have he := (scaleExponent_bounds hσ hs (Nat.succ_le_of_lt hj)).2
  have hd := amplitudeExponent_lower j
  have hs' : 0 < (steps : ℝ) := by exact_mod_cast (by omega : 0 < steps)
  rw [amplitudeExponent_succ]
  refine ⟨by linarith,by linarith,lt_min (div_pos hσ hs') (by norm_num)⟩

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PrimitiveInitialMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar contraction starts the primitive mean iteration.
Its normalized defect is only the polynomial perturbation divided by δ². -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PhaseMean

lemma primitiveSeed_smooth (δ : ℝ) {F : JetPolynomial.Base → JetPolynomial.Space}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (primitiveSeed δ F) := hF.const_smul _

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveSeedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact jet range and derivative profiles for all scalar seeds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial WeightedEstimates

lemma primitiveSeed_factor_bound {δ : ℝ} (hδ : δ^2 ≤ 1) :
    |Real.sqrt (1-δ^2)| ≤ 1 ∧ |Real.sqrt (1-δ^2)-1| ≤ δ^2 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hδ)
  have hn := Real.sqrt_nonneg (1-δ^2)
  have hu : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  rw [abs_of_nonneg hn,abs_of_nonpos (sub_nonpos.mpr hu)]
  exact ⟨hu,by nlinarith⟩

theorem compact_primitiveSeed_bounds {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {F : JetPolynomial.Base → JetPolynomial.Space}
    (hF : ContDiff ℝ ∞ F) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∃ A B : ℕ → ℝ,
      (∀ m, 1 ≤ A m) ∧ (∀ m, 1 ≤ B m) ∧
      ∀ δ : ℝ, δ^2 ≤ 1 → Set.MapsTo (lowJet (primitiveSeed δ F)) U Q ∧
        (∀ m, WeightedBound U 1 m (B m) (lowJet (primitiveSeed δ F))) ∧
        (∀ m, WeightedBound U 1 (m+2) (A m) (primitiveSeed δ F)) ∧
        (∀ m, WeightedBound U 1 m (A m * δ^2) (primitiveSeed δ F-F)) := by
  choose A hA ha using fun m => compact_local_weighted_bound hU isOpen_univ K.isCompact
    hUK (Set.subset_univ _) hF.contDiffOn (m+2)
  choose D hD hd using fun m => bounded_lowJet_prefix hU K hUK m
  obtain ⟨Q,hQ,hQG⟩ := bounded_lowJet_range hU K hUK (zero_le_one.trans (hA 0))
  refine ⟨Q,hQ,A,(fun m => D m+A m),hA,?_,?_⟩
  · intro m
    exact (hD m).trans (le_add_of_nonneg_right (zero_le_one.trans (hA m)))
  · intro δ hδ
    have hfactor := primitiveSeed_factor_bound hδ
    have hseed (m : ℕ) : WeightedBound U 1 (m+2) (A m) (primitiveSeed δ F) := by
      apply ((ha m 1 zero_le_one le_rfl).const_smul hU.uniqueDiffOn hF.contDiffOn
        (Real.sqrt (1-δ^2))).mono_const
      exact mul_le_of_le_one_left (zero_le_one.trans (hA m)) hfactor.1
    refine ⟨hQG _ (primitiveSeed_smooth δ hF) (hseed 0),?_,hseed,?_⟩
    · intro m
      apply hd m _ (primitiveSeed_smooth δ hF) 1 (A m) zero_lt_one le_rfl
        (zero_le_one.trans (hA m))
      intro j hj
      simpa only [one_pow,div_one] using (hseed m).mono_order hj
    · intro m
      have hb := ((ha m 1 zero_le_one le_rfl).mono_order (by omega : m ≤ m+2)).const_smul
        hU.uniqueDiffOn hF.contDiffOn (Real.sqrt (1-δ^2)-1)
      apply (hb.mono_const (by
        calc
          |Real.sqrt (1-δ^2)-1| * A m ≤ δ^2 * A m :=
            mul_le_mul_of_nonneg_right hfactor.2 (zero_le_one.trans (hA m))
          _ = A m * δ^2 := mul_comm _ _)).congr
      intro x _
      ext k
      simp only [primitiveSeed,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveSeedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local jets and global displacement of the actual contracted
primitive seed, and its initial normalized polynomial defect. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance primitiveSeedFiberNormed_r1962b4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveSeedFiberSpace_r1962b4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveSeedDualAdd_r1962b4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveSeedDualSmul_r1962b4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance primitiveSeedSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveSeedSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_const_smul (i : A.centers) (c : ℝ) (F : M → Space) :
    A.jetChartMap i (c • F) = c • A.jetChartMap i F := by
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (c • F) x) =
    c • spaceCoordinates (localize (i : M) (A.outer i) F x)
  rw [localize_smul]
  exact map_smul spaceCoordinates c _

omit [CompactSpace M] in
lemma jetChartMap_primitiveSeed (i : A.centers) (δ : ℝ) (F : M → Space) :
    A.jetChartMap i (Real.sqrt (1-δ^2) • F) = primitiveSeed δ (A.jetChartMap i F) := by
  rw [A.jetChartMap_const_smul]
  rfl

/-- The compact low-jet range, all local derivative profiles, and the global
quadratic displacement profile are chosen before the contraction parameter. -/
theorem atlas_primitive_seed_bounds
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (K : A.centers → Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ K i) :
    ∃ Q : Set LowJet, IsCompact Q ∧
    ∃ J B : A.centers → ℕ → ℝ, ∃ D : ℕ → ℝ,
      (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ B i m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ δ : ℝ, δ^2 ≤ 1 →
        ContMDiff planeModel spaceModel ∞ (Real.sqrt (1-δ^2) • F) ∧
        (∀ i, MapsTo (lowJet (A.jetChartMap i (Real.sqrt (1-δ^2) • F))) (U i) Q) ∧
        (∀ i m, WeightedEstimates.WeightedBound (U i) 1 m (B i m)
          (lowJet (A.jetChartMap i (Real.sqrt (1-δ^2) • F)))) ∧
        (∀ i m, WeightedEstimates.WeightedBound (U i) 1 (m+2) (J i m)
          (A.jetChartMap i (Real.sqrt (1-δ^2) • F))) ∧
        (∀ m, A.WeightedBound 1 m (D m * δ^2) (Real.sqrt (1-δ^2) • F-F)) := by
  classical
  choose Q hQ J B hJ hB hlocal using fun i =>
    compact_primitiveSeed_bounds (hU i) (K i) (hUK i) (A.jetChartMap_smooth i hF)
  choose D hD hglobal using fun m => A.exists_shifted_bound m 0 hF
  let Q₀ : Set LowJet := ⋃ i, Q i
  refine ⟨Q₀,isCompact_iUnion hQ,J,B,D,hJ,hB,hD,?_⟩
  intro δ hδ
  have hseed (i) := hlocal i δ hδ
  have hid (i) := A.jetChartMap_primitiveSeed i δ F
  refine ⟨space_smul_contMDiff hF _,?_,?_,?_,?_⟩
  · intro i x hx
    rw [hid i]
    exact mem_iUnion.mpr ⟨i,(hseed i).1 hx⟩
  · intro i m
    rw [hid i]
    exact (hseed i).2.1 m
  · intro i m
    rw [hid i]
    exact (hseed i).2.2.1 m
  · intro m
    have hb : A.WeightedBound 1 m (D m) F := A.shifted_zero_to_weighted (hglobal m)
    have hh := A.weightedBound_const_smul hF hb (Real.sqrt (1-δ^2)-1)
    have heq : Real.sqrt (1-δ^2) • F-F = (Real.sqrt (1-δ^2)-1) • F := by
      rw [sub_smul,one_smul]
    rw [heq]
    intro i
    apply (hh i).mono_const
    calc
      |Real.sqrt (1-δ^2)-1| * D m ≤ δ^2 * D m :=
        mul_le_mul_of_nonneg_right (primitiveSeed_factor_bound hδ).2 (hD m)
      _ = D m * δ^2 := mul_comm _ _

/-- The normalized defect of the contracted seed is globally of order
`ε/δ²`, with a fixed all-order profile. -/
theorem atlas_primitive_seed_defect_bounds {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (K : A.centers → Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ K i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) :
    ∃ D E : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
      ∀ (δ ε : ℝ), δ ≠ 0 → δ^2 ≤ 1 → 0 ≤ ε → ε ≤ 1 →
        (∀ m, A.WeightedBound 1 m (D m * δ^2) (Real.sqrt (1-δ^2) • F-F)) ∧
        (∀ m, A.TensorWeightedBound 1 m (E m * ε / δ^2)
          (A.normalizedPolynomialDefect P ε δ (inducedTensor F)
            (Real.sqrt (1-δ^2) • F))) := by
  obtain ⟨Q,hQ,J,B,D,hJ,hB,hD,hseed⟩ := A.atlas_primitive_seed_bounds F hF U hU K hUK
  obtain ⟨E,hE,hvalue⟩ := A.atlas_polynomial_value_bounds P hP U hU houter (fun _ => Q)
    (fun _ => hQ) (fun i m => B i (m+tensorOrder (P i)))
    (fun i m => hB i (m+tensorOrder (P i)))
  refine ⟨D,E,hD,hE,?_⟩
  intro δ ε hδ hδ1 hε hε1
  obtain ⟨hG,hGQ,hGb,_,hdisp⟩ := hseed δ hδ1
  refine ⟨hdisp,?_⟩
  intro m
  have hv := hvalue (Real.sqrt (1-δ^2) • F) hG hGQ 1 ε zero_lt_one le_rfl hε hε1
    (fun i m => hGb i (m+tensorOrder (P i))) m
  have hh := A.tensorWeightedBound_const_smul (A.atlasPolynomialValue_smooth hP hG ε) hv
    (-(δ^2)⁻¹)
  rw [← A.normalizedPolynomialDefect_seed P ε hF hδ hδ1] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ))]
  simp only [one_pow,div_one]
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveInitialFamily
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete starting family for the finite primitive iteration.
At amplitude z^(1/4), both its C2 displacement and its normalized mean
defect are bounded by fixed multiples of z^(1/2). -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates

lemma initial_amplitude_square {z : ℝ} (hz : 0 < z) :
    (z^(1/4 : ℝ))^2 = z^(1/2 : ℝ) := by
  rw [← Real.rpow_mul_natCast hz.le]
  norm_num

lemma initial_error_quotient {z : ℝ} (hz : 0 < z) :
    z/(z^(1/4 : ℝ))^2 = z^(1/2 : ℝ) := by
  rw [initial_amplitude_square hz]
  calc
    z / z^(1/2 : ℝ) = z^(1 : ℝ)/z^(1/2 : ℝ) := by rw [Real.rpow_one]
    _ = z^((1 : ℝ)-1/2) := (Real.rpow_sub hz _ _).symm
    _ = z^(1/2 : ℝ) := by norm_num

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSlowFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite family solving the perturbed mean equation to successively
higher amplitude orders. Every member is an actual smooth map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma polynomial_slow_seed {n : A.centers → ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.HasPolynomialSlowFamily Pol (inducedTensor F) F (1/4) 0 := by
  classical
  obtain ⟨U,K,hU,hUK,_,houter⟩ := A.exists_outer_domains
  obtain ⟨L,D,hL,hD,hseed⟩ := A.atlas_primitive_seed_defect_bounds Pol hPol F hF U hU K hUK houter
  choose P hP hPF using fun m => A.exists_shifted_bound 2 m hF
  refine ⟨1/2,1/2,1,L 3,P,D,by norm_num,by norm_num,zero_lt_one,le_rfl,
    hL 3,hP,hD,hPF,?_⟩
  intro z hz hz1
  have hδ : 0 < z^(1/4 : ℝ) := Real.rpow_pos_of_pos hz _
  have hδ1 : (z^(1/4 : ℝ))^2 ≤ 1 := by
    rw [initial_amplitude_square hz]
    exact Real.rpow_le_one hz.le hz1.le (by norm_num)
  obtain ⟨hclose,hdefect⟩ := hseed (z^(1/4 : ℝ)) z hδ.ne' hδ1 hz.le hz1.le
  have hsqrt : |Real.sqrt (1-(z^(1/4 : ℝ))^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hδ1),Real.sqrt_nonneg (1-(z^(1/4 : ℝ))^2)]
  refine ⟨Real.sqrt (1-(z^(1/4 : ℝ))^2) • F,space_smul_contMDiff hF _,?_,?_,?_⟩
  · simpa only [initial_amplitude_square hz] using hclose 3
  · intro m
    simpa only [Real.rpow_zero] using
      A.shiftedBound_smul_of_abs_le_one hF zero_le_one (hP m) hsqrt (hPF m)
  · intro m
    have he : D m*z/(z^(1/4 : ℝ))^2 = D m*z^(1/2 : ℝ) := by
      rw [mul_div_assoc,initial_error_quotient hz]
    simpa only [Real.rpow_zero,he] using hdefect m

end SmoothingAtlas

namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- The number of stages and the loss determine the slow scales before any
accuracy order. This finite induction uses only constructed increments. -/
theorem polynomial_finite_slow_family (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (steps : ℕ) (hsteps : 1 ≤ steps) (σmax : ℝ) (hσmax : 0 < σmax) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1/16 ∧ σ < σmax ∧ ∀ j : ℕ, j ≤ steps →
      data.A.HasPolynomialSlowFamily Pol g.inner F (amplitudeExponent j) (scaleExponent σ steps j) := by
  obtain ⟨loss,hstep⟩ := data.polynomial_slow_step Pol hPol hF
  obtain ⟨σ₀,hσ₀,_,_,hσ₀loss,hσ₀16,_⟩ := exists_slow_exponent 0 0 1 (by norm_num) (loss : ℝ) 0
  let σ := min σ₀ (σmax/2)
  have hσ : 0 < σ := lt_min hσ₀ (half_pos hσmax)
  have hσ16 : σ < 1/16 := (min_le_left _ _).trans_lt hσ₀16
  have hσσmax : σ < σmax := (min_le_right _ _).trans_lt (half_lt_self hσmax)
  have hσloss : σ*(loss : ℝ) < 1/2 := (mul_le_mul_of_nonneg_right
    (min_le_left σ₀ (σmax/2)) (Nat.cast_nonneg loss : (0 : ℝ) ≤ loss)).trans_lt hσ₀loss
  refine ⟨σ,hσ,hσ16,hσσmax,?_⟩
  intro j hj
  induction j with
  | zero =>
      simpa only [amplitudeExponent_zero,scaleExponent,Nat.cast_zero,zero_mul,zero_div,hmetric] using
        data.A.polynomial_slow_seed Pol hPol F hF
  | succ j ih =>
      have hjlt : j < steps := by omega
      obtain ⟨a,u,η,L,P,D,ha,hu,hη,hη1,hL,hP,hD,hPF,hfamily⟩ := ih (by omega)
      have hb := (scaleExponent_bounds hσ hsteps (by omega : j ≤ steps)).1
      have hb' := (scaleExponent_bounds hσ hsteps (by omega : j+1 ≤ steps)).2
      have hscale : scaleExponent σ steps j < scaleExponent σ steps (j+1) := by
        have hdiff := scaleExponent_step (σ := σ) (steps := steps) (j := j)
        have hd : 0 < σ/(steps : ℝ) := div_pos hσ (by exact_mod_cast (by omega : 0 < steps))
        linarith
      have hloss : scaleExponent σ steps (j+1)*(loss : ℝ) < 1 := by
        have hh := mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg loss : (0 : ℝ) ≤ loss)
        linarith
      have hpositives := slow_step_positive_powers hσ hσ16 hsteps hjlt
      have hbd : 2*scaleExponent σ steps (j+1) < amplitudeExponent j := by
        have hd := amplitudeExponent_lower j
        linarith
      have hdd : amplitudeExponent j < amplitudeExponent (j+1) := by
        rw [amplitudeExponent_succ]
        linarith [amplitudeExponent_pos j]
      obtain ⟨a',η',L',P',D',ha',hη',hη'1,hL',hP',hD',hnext⟩ :=
        hstep (scaleExponent σ steps j) (scaleExponent σ steps (j+1))
          (amplitudeExponent j) (amplitudeExponent (j+1)) a u hb hscale hloss hbd hdd
          (by linarith [hpositives.1]) ha hu P D L hP hD hL hPF
      let R : ℕ → ℝ := fun m => max (P' m) (P m)
      refine ⟨a',min u (amplitudeExponent j-2*scaleExponent σ steps (j+1)),min η η',L',R,D',
        ha',lt_min hu (sub_pos.mpr hbd),lt_min hη hη',
        (min_le_left _ _).trans hη1,hL',?_,hD',?_,?_⟩
      · intro m
        exact (hP' m).trans (le_max_left _ _)
      · intro m i k hk x
        exact (hPF m i k hk x).trans (le_max_right _ _)
      · intro z hz hzmin
        obtain ⟨G,hG,hclose,hmap,hdefect⟩ := hfamily z hz (hzmin.trans_le (min_le_left _ _))
        obtain ⟨G',hG',hclose',hmap',hdefect'⟩ := hnext z hz
          (hzmin.trans_le (min_le_right _ _)) G hG hclose hmap hdefect
        refine ⟨G',hG',hclose',?_,hdefect'⟩
        intro m i k hk x
        exact (hmap' m i k hk x).trans (le_max_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanApproximation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slow iteration solves the actual restored polynomial mean
metric to any prescribed finite unweighted order. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberSpace
local instance meanApproxDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberSpace
local instance meanApproxSectionNormed_r1962b4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance meanApproxSectionSpace_r1962b4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorWeightedBound_unscaled {H : ∀ x : M, CovariantTwoTensor x}
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hH : A.TensorWeightedBound s m C H) : A.TensorWeightedBound 1 m (C/s^m) H := by
  intro i j hj x hx
  simp only [one_pow,one_mul]
  exact ((hH i).deriv_le hs hj hx).trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 hj))

lemma polynomial_metric_error_of_defect {n : A.centers → ℕ}
    {Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    {ε δ s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hδ : δ ≠ 0)
    (hbase : A.TensorWeightedBound s m C γ)
    (hdefect : A.TensorWeightedBound s m D (A.normalizedPolynomialDefect Pol ε δ γ G)) :
    A.TensorWeightedBound s m (δ^2*(C+D)) (A.atlasPolynomialMetric Pol ε G-γ) := by
  have hd := A.normalizedPolynomialDefect_smooth (ε := ε) (δ := δ) hPol hγ hG
  have hh := A.tensorWeightedBound_const_smul (hγ.add_section hd)
    (A.tensorWeightedBound_add hγ hd hs hbase hdefect) (-(δ^2))
  have heq : A.atlasPolynomialMetric Pol ε G-γ =
      (-(δ^2)) • (γ+A.normalizedPolynomialDefect Pol ε δ γ G) := by
    funext x
    ext v w
    change A.atlasPolynomialMetric Pol ε G x v w-γ x v w =
      -(δ^2)*(γ x v w+((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric Pol ε G x v w)-γ x v w))
    field_simp
    ring
  rw [heq]
  simpa only [abs_neg,abs_of_nonneg (sq_nonneg δ)] using hh

end SmoothingAtlas
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxDualSmul
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberSpace
local instance meanApproxSectionNormed_r1962b4_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance meanApproxSectionSpace_r1962b4_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Finite-order approximation of the actual polynomial mean, with all
slow-map derivative profiles and a vanishing C3 displacement. -/
theorem polynomial_mean_approximation_oai (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (R N : ℕ) (σmax : ℝ) (hσmax : 0 < σmax) :
    ∃ (b u η L C : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ b < σmax ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ (∀ m, 0 ≤ P m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∃ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G ∧
      data.A.WeightedBound 1 3 (L*z^u) (G-F) ∧
      (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) ∧
      data.A.TensorWeightedBound 1 R (C*z^N) (data.A.atlasPolynomialMetric Pol z G-g.inner) := by
  obtain ⟨steps,hsteps,horder⟩ := exists_amplitude_steps R N
  obtain ⟨σ,hσ,hσ16,hσσmax,hfamily⟩ :=
    data.polynomial_finite_slow_family Pol hPol hF hmetric steps hsteps σmax hσmax
  obtain ⟨a,u,η,L,P,D,ha,hu,hη,hη1,hL,hP,hD,_,hfamily⟩ := hfamily steps le_rfl
  obtain ⟨K,hK,hbase⟩ := data.A.exists_bundle_bound data.A.tensorTriv data.A.tensorTriv_domain R g.contMDiff
  let b := scaleExponent σ steps steps
  have hb := (scaleExponent_bounds hσ hsteps (le_refl steps)).1
  have hbσ := (scaleExponent_bounds hσ hsteps (le_refl steps)).2
  have hpow : (N : ℝ) ≤ 2*amplitudeExponent steps-b*(R : ℝ) := by
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hb1 : b ≤ 1 := by dsimp [b] <;> linarith
    have hh : b*(R : ℝ) ≤ R := by nlinarith
    linarith
  refine ⟨b,u,η,L,K+D R,P,hb,hbσ.trans_lt hσ16,hbσ.trans_lt hσσmax,hu,hη,hη1,hL,add_nonneg hK (hD R),hP,?_⟩
  intro z hz hzη
  have hz1 := hzη.le.trans hη1
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  obtain ⟨G,hG,hclose,hmap,hdefect⟩ := hfamily z hz hzη
  have hδ : 0 < z^amplitudeExponent steps := Real.rpow_pos_of_pos hz _
  have hDb : data.A.TensorWeightedBound (z^b) R (D R)
      (data.A.normalizedPolynomialDefect Pol z (z^amplitudeExponent steps) g.inner G) := by
    intro i
    apply (hdefect R i).mono_const
    exact mul_le_of_le_one_right (hD R) (Real.rpow_le_one hz.le hz1 ha.le)
  have herror := data.A.polynomial_metric_error_of_defect hPol g.contMDiff hG hs.le hδ.ne'
    (fun i => (hbase i).shrink_scale hs.le hs1) hDb
  have he := data.A.tensorWeightedBound_unscaled hs hs1
    (mul_nonneg (sq_nonneg _) (add_nonneg hK (hD R))) herror
  refine ⟨G,hG,hclose,hmap,fun i => (he i).mono_const ?_⟩
  have heq : (z^amplitudeExponent steps)^2*(K+D R)/(z^b)^R =
      (K+D R)*z^(2*amplitudeExponent steps-b*R) := by
    rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_mul_natCast hz.le]
    rw [mul_comm (z^_) _,mul_div_assoc,← Real.rpow_sub hz]
    congr 2
    ring
  rw [heq]
  simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hz hz1 hpow) (add_nonneg hK (hD R))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_oai.{u_1}
