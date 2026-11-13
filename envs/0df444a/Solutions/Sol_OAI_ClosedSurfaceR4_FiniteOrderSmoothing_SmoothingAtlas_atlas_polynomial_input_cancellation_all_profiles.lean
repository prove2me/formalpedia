-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:24.941347+00:00
-- url     : https://prove2.me/submissions/22c0dae3-d7af-497f-af79-1fde8486e292

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
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_exists_solution
import Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_CompactPhaseFamily_uniform_polynomial_solvers_all_profiles

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
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




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

end Quantitative
end ClosedSurfaceR4.SmallModes

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

lemma WeightedBound.indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    WeightedBound univ s m C (U.indicator f) := by
  classical
  apply WeightedBound.extend_support hU ((tsupport_indicator_subset hK hz).trans hKU) hC
  apply hb.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

lemma continuous_gramDet_field {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have hx := (contDiff_real_coordDeriv hF dx).continuous
  have hy := (contDiff_real_coordDeriv hF dy).continuous
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma good_eventually {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} {p : X}
    (hB : ContinuousAt B p) (hξ : ContinuousAt ξ p) (hg : Good (B p) (ξ p)) :
    ∀ᶠ q in 𝓝 p, Good (B q) (ξ q) := by
  have ho : IsOpen {z : (Fin 3 → RVec n) × Base | Good z.1 z.2} :=
    isOpen_good continuous_fst continuous_snd
  exact (hB.prodMk hξ).preimage_mem_nhds (ho.mem_nhds hg)




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem smooth_extension_near {F : M → V} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ F U) {p : M} (hp : p ∈ U) :
    ∃ G : M → V, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ U ∧ G =ᶠ[𝓝 p] F := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hU.mem_nhds hp)
  let G : M → V := fun q => b q • F q
  have hs : tsupport G ⊆ tsupport b := tsupport_smul_subset_left _ _
  refine ⟨G, ?_, ?_, hs.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro q hq
    exact b.contMDiffAt.smul ((hF q (hb (hs hq))).contMDiffAt
      (hU.mem_nhds (hb (hs hq))))
  · exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hs
  · filter_upwards [b.eventuallyEq_one] with q hq
    simp only [G, hq, Pi.one_apply, one_smul]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
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

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (w p : Base) :
    coordDeriv w (F ∘ φ) p = fderiv ℝ F (φ p) (coordDeriv w φ p) := by
  simp only [coordDeriv,fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ φ)) p =
      coordDeriv (fderiv ℝ φ p v) (coordDeriv (fderiv ℝ φ p w) F) (φ p) +
      fderiv ℝ F (φ p) (coordDeriv v (coordDeriv w φ) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := ((hDF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (φ p)).hasFDerivAt.comp p
    ((hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt
  have hD2 := ((contDiffAt_coordDeriv (p := p) hφ.contDiffAt w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ F ∘ φ) q (coordDeriv w φ q)) = coordDeriv w (F ∘ φ) := by
    funext q
    exact (coordDeriv_comp_smooth hF hφ w q).symm
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  rw [real_second_coordDeriv ((hDF.differentiable (by simp)) (φ p))]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm] using heval

lemma realNormalPart_fderiv {F : RField 4} (p v : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (fderiv ℝ F p v) = 0 := by
  change realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v F p) = 0
  conv_lhs => arg 3; rw [coordDeriv_eq_basis F v p]
  have hl := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hl.map_add,hl.map_smul,hl.map_smul,realNormalPart_self_left _ _ hD,
    realNormalPart_self_right _ _ hD,smul_zero,smul_zero,add_zero]



lemma realSecondForm_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ,
    second_coordDeriv_comp_smooth hF hφ]
  change realNormalPart (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) _ = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    realNormalPart_change_basis _ _ _ _ _ _ _ hD hdet]
  rw [(realNormalPart_linear _ _).map_add,realNormalPart_fderiv _ _ hD,add_zero]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

lemma rotated_pullCovector (A : Base →L[ℝ] Base) (ξ : Base) :
    A (-(pullCovector A ξ).2,(pullCovector A ξ).1) = coordDet A • (-ξ.2,ξ.1) := by
  rw [linear_apply_basis]
  ext <;> simp [pullCovector,coordDet,Prod.smul_mk] <;> ring

lemma phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1) =
      (coordDet (fderiv ℝ φ p))^2 •
        secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1) := by
  rw [← realSecondForm_quadratic (hF.comp hφ),realSecondForm_comp_smooth hF hφ _ _ _ hD hdet,
    rotated_pullCovector,realSecondForm_quadratic hF,secondQuadratic_smul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearized_add_right {n : ℕ} {F X Y : RField n} {p : Base}
    (hX : DifferentiableAt ℝ X p) (hY : DifferentiableAt ℝ Y p) (v w : Base) :
    realLinearized F (fun q => X q + Y q) v w p =
      realLinearized F X v w p + realLinearized F Y v w p := by
  simp only [realLinearized, partial_add hX hY, dotProduct_add]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PullbackBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)
open ClosedSurfaceR4.QuadraticMean (weighted_real_complex)

lemma weighted_base_fst {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).1) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.fst ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))

lemma weighted_base_snd {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).2) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.snd ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))

lemma weighted_complexEvaluate {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → ComplexTensor} {v w : Base → Base} {s C D B : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hbA : WeightedBound U s m C A) (hbv : WeightedBound U s m D v)
    (hbw : WeightedBound U s m B w) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * B))
      (fun p => complexEvaluate (A p) (v p) (w p)) := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have hvcB := weighted_real_complex hU hs hD hv.fst (weighted_base_fst hU hs hD hv hbv)
  have hvdB := weighted_real_complex hU hs hD hv.snd (weighted_base_snd hU hs hD hv hbv)
  have hwcB := weighted_real_complex hU hs hB hw.fst (weighted_base_fst hU hs hB hw hbw)
  have hwdB := weighted_real_complex hU hs hB hw.snd (weighted_base_snd hU hs hB hw hbw)
  have h0s := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1s := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2s := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  have h0 := ((hbA.component hU hs hC hA 0).mul hU hs hC hD
    (contDiffOn_pi.mp hA 0) hvc hvcB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 0).mul hvc) hwc hwcB
  have h2 := ((hbA.component hU hs hC hA 2).mul hU hs hC hD
    (contDiffOn_pi.mp hA 2) hvd hvdB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 2).mul hvd) hwd hwdB
  have h11 := hvcB.mul hU hs hD hB hvc hwd hwdB
  have h12 := hvdB.mul hU hs hD hB hvd hwc hwcB
  have h1 := (hbA.component hU hs hC hA 1).mul hU hs hC (by positivity)
    (contDiffOn_pi.mp hA 1) ((hvc.mul hwd).add (hvd.mul hwc))
    (h11.add hU hs (hvc.mul hwd) (hvd.mul hwc) h12)
  have hh := (h0.add hU hs h0s h1s h1).add hU hs (h0s.add h1s) h2s h2
  convert hh using 1 <;> first | rfl | ring

lemma weighted_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => complexPullbackField e p (A p)) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    (contDiffOn_pi.mp (contDiffOn_complexPullbackField_apply hU hA he))
  intro i
  exact weighted_complexEvaluate hU.uniqueDiffOn hs.le hC hD hD hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i)) hbA
    (hbe _ (firstDirection_norm i)) (hbe _ (secondDirection_norm i))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open Set ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realLinearizedTensor_congr_right {n : ℕ} {F X Y : RField n} {p : Base}
    (h : X =ᶠ[nhds p] Y) : realLinearizedTensor F X p = realLinearizedTensor F Y p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]

lemma realLinearizedTensor_zero_right {n : ℕ} (F : RField n) (p : Base) :
    realLinearizedTensor F (fun _ => 0) p = 0 := by
  ext i
  simp [realLinearizedTensor_apply, realLinearized, coordDeriv]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_UniformMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.RootMean



lemma weighted_coordDeriv_of_jets {U : Set Base} (hU : IsOpen U)
    {f : Base → Base} (hf : ContDiffOn ℝ ∞ f U) {τ D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ j f U p‖ ≤ D) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U τ m D (coordDeriv v f) := by
  have hd : WeightedBound U τ m D (fderivWithin ℝ f U) := by
    intro j hj p hp
    rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hp]
    exact (mul_le_mul_of_nonneg_left (hb (j+1) (by omega) (by omega) p hp)
      (pow_nonneg hτ j)).trans (mul_le_of_le_one_left hD (pow_le_one₀ hτ hτ1))
  have hh := hd.clm_apply_const hU.uniqueDiffOn hτ
    (hf.fderivWithin hU.uniqueDiffOn le_rfl) v
  apply (hh.mono_const (mul_le_of_le_one_left hD hv)).congr
  intro p hp
  simp only [coordDeriv, fderivWithin_of_isOpen hU hp]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

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
local instance planeReadSectionSpace_r95c9e6_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

lemma tensorChartPush_bound (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {s : ℝ≥0} {J D : ℝ} {m : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm)) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (tensorChartPush e hi K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm K s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm K s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source).comp_coordinates
    e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ hN hi
    f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  have ht := weighted_complexPullbackField_apply e.open_target hs (by positivity) hD
    (f.contDiff.comp_contDiffOn hi) hi hb hfield
  have hg := ht.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (tensorChartPush_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteProfileBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit terminal derivative orders in finite error profiles. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_terminal (L : ℕ) (K C f : ℕ → ℝ) (j m : ℕ) :
    boundProfile L K (fun r => C r * f (r + L)) j m =
      boundProfile L K C j m * f (m + (j + 1) * L) := by
  induction j generalizing m with
  | zero => simp only [boundProfile, zero_add, one_mul]
  | succ j ih =>
    rw [boundProfile, ih, boundProfile]
    have he : m + L + (j + 1) * L = m + (j + 1 + 1) * L := by ring
    rw [he, mul_assoc]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

namespace Perturbation

lemma linearized_add {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (p : Base) :
    linearized P ε G (fun x => H x + K x) t p =
      linearized P ε G H t p + linearized P ε G K t p := by
  simp only [linearized, Expression.variation_add _ G hH hK, mul_add, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedForcedSize
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite forced correction has a scale-independent amplitude
budget. Only the finite number of required input derivatives grows. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma forcedModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) : 0 ≤ forcedModeBudget n L B D q m := by
  apply add_nonneg (initialConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)) _ _

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full linearized metric perturbation preserves the support of its
varying field, including every higher-jet polynomial term. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero_of_notMem {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {p : SmallModes.Base} (hp : p ∉ tsupport X) :
    coordinateFullLinearized P ε G X p = 0 := by
  have hx : X =ᶠ[nhds p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : (X ∘ planeCoordinateIsometry) =ᶠ[nhds (planeCoordinateIsometry.symm p)] (fun _ => 0) := by
    apply hx.comp_tendsto
    simpa only [planeCoordinateIsometry.apply_symm_apply] using
      (planeCoordinateIsometry.continuous.continuousAt (x := planeCoordinateIsometry.symm p)).tendsto
  have hn : planeCoordinateIsometry.symm p ∉ tsupport (X ∘ planeCoordinateIsometry) :=
    notMem_tsupport_iff_eventuallyEq.mpr hc
  have hm : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X p = 0 := by
    rw [RealModes.realLinearizedTensor_congr_right hx, RealModes.realLinearizedTensor_zero_right]
  funext k
  simp only [coordinateFullLinearized, Pi.add_apply, hm, Pi.zero_apply, zero_add,
    coordinateRealLinearized, linearized]
  apply Finset.sum_eq_zero
  intro l _
  rw [(P k l).variation_zero_of_notMem G hn 0, mul_zero]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorPlaneRestore
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRestore_smooth (f : A.centers → SmallModes.Base → V)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.vectorPlaneRestore f) := by
  have hh : ContMDiff planeModel 𝓘(ℝ, V) ∞
      (fun x => ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry) x) :=
    ContMDiff.sum (fun i _ => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [vectorPlaneRestore, Finset.sum_apply]

variable [CompactSpace M]

theorem vectorPlaneRestore_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : A.centers → SmallModes.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.WeightedBound s m (D*C) (A.vectorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i => f i ∘ planeCoordinateIsometry) s C hs hs1 hC
    (fun i => (hf i).comp planeCoordinateIsometry.contDiff)
    (fun i => weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullLinearized P ε G (X + Y) =
      coordinateFullLinearized P ε G X + coordinateFullLinearized P ε G Y := by
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullLinearized, Pi.add_apply, coordinateRealLinearized,
    RealModes.realLinearizedTensor_apply]
  rw [hc, linearized_add _ ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff), ha,
    RealModes.realLinearized_add_right (hX.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hY.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additivity and smoothness of the actual full linearized operator.
Coefficient smoothness is required only near the support of the variation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) :
    coordinateFullLinearized P ε G 0 = 0 := by
  funext p
  exact coordinateFullLinearized_zero_of_notMem P ε G (by simp)

lemma coordinateFullLinearized_sum {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (a : Finset ι) (X : ι → RealModes.RField 4) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    coordinateFullLinearized P ε G (fun p => ∑ i ∈ a, X i p) =
      fun p => ∑ i ∈ a, coordinateFullLinearized P ε G (X i) p := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change coordinateFullLinearized P ε G 0 = 0
    exact coordinateFullLinearized_zero P ε G
  | @insert i a hi ih =>
    have hs : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, X j p) := ContDiff.sum fun j _ => hX j
    simp only [Finset.sum_insert hi]
    change coordinateFullLinearized P ε G (X i + fun p => ∑ j ∈ a, X j p) = _
    rw [coordinateFullLinearized_add P ε G (hX i) hs, ih]
    rfl

lemma coordinateFullLinearized_smooth {n : ℕ} {O : Set LowJet} {U : Set Base}
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {X : RealModes.RField 4} (hX : ContDiff ℝ ∞ X)
    (hXs : tsupport X ⊆ (modeSupport K : Set SmallModes.Base)) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  let Xs : SupportedField (F := Fin 4 → ℝ) (modeSupport K) :=
    ContDiffMapSupportedIn.of_support_subset hX (subset_closure.trans hXs)
  let Xp := pullSupported planeCoordinateIsometry K Xs
  have hp : ContDiff ℝ ∞ (coordinateRealLinearized P ε G X 0) := by
    apply contDiff_pi.mpr
    intro k
    have hs : ContDiff ℝ ∞ (fun x => ∑ l, ε ^ (l.val + 1) * (P k l).variation G Xp (x, 0)) :=
      ContDiff.sum (s := Finset.univ) (fun l _ =>
      contDiff_const.mul ((P k l).variation_smooth_global hO hU K.isCompact.isClosed hKU
        (hP k l) hG Xp.contDiff hQ Xp.tsupport_subset 0))
    exact hs.comp planeCoordinateIsometry.symm.contDiff
  exact (contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add hp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FinitePolynomialCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cancellation by the actual polynomial phase solvers. All
summands are constructed with one common accuracy and wavelength. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem finite_polynomial_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ) (K : ι → Compacts Base)
    {τ : ℝ} {s : ℝ≥0} (c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : ∀ i, SupportedField (F := ComplexTensor) (modeSupport (K i))) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧
      tsupport X ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).size (f i) q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).residual (f i) q m)
        (fun x => coordinateFullLinearized P ε G X x +
          ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
  classical
  choose X hsm hsp hb hr using fun i => (c i).exists_solution hτ hs hτs hs1 hε hsmall (f i) q
  refine ⟨(fun p => ∑ i, X i p), ContDiff.sum (fun i _ => hsm i), ?_, ?_, ?_⟩
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
    intro p hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport (fun hx => hn (Set.mem_iUnion.mpr ⟨i, hsp i hx⟩))
  · intro m
    exact WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (hsm i).contDiffOn) (fun i _ => hb i m)
  · intro m
    have he : (fun x => coordinateFullLinearized P ε G (fun p => ∑ i, X i p) x +
        ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x) =
        (fun x => ∑ i, (coordinateFullLinearized P ε G (X i) x +
          QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
      rw [coordinateFullLinearized_sum P ε G Finset.univ X hsm]
      funext x
      exact Finset.sum_add_distrib.symm
    rw [he]
    apply WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => ?_) (fun i _ => hr i m)
    exact ((coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
      (c i).mapsG (K i) (c i).supportU (hsm i) (hsp i) ε).add
      (contDiffOn_univ.mp (RealModes.contDiffOn_displacement
        (((c i).smoothPhase.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
        (f i).contDiff.contDiffOn τ))).contDiffOn

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveFactors
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the finite input norm and the small residual power from the
geometric solver constants. The input order is explicit. -/
noncomputable section
open scoped NNReal ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma size_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.size f q m = c.sizeFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold size sizeFactor inputOrder
  ring

lemma residual_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.residual f q m = (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      c.residualFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold residual residualFactor inputOrder
  rw [FiniteParametrix.boundProfile_terminal]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_r95c9e6_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_r95c9e6_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_r95c9e6_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_r95c9e6_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_r95c9e6_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_r95c9e6_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPhaseChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncritical smooth phase is the first coordinate of a smooth local chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseLinear_phaseDerivative (φ : Base → ℝ) (p : Base) :
    phaseLinear (phaseDerivative φ p) = fderiv ℝ φ p := by
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,phaseLinear_apply,phaseDerivative]
  ring

/-- The chart is globally smooth as a function, and its inverse is smooth on
its target. Later cutoff extensions can make the inverse globally smooth. -/
theorem exists_smooth_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let L := phaseEquiv (phaseDerivative φ p) hp
  let f : Base → Base := fun x => (φ x,(L x).2)
  have hf : ContDiff ℝ ∞ f := hφ.prodMk (contDiff_snd.comp L.contDiff)
  have hφ' : HasFDerivAt φ (phaseLinear (phaseDerivative φ p)) p := by
    rw [phaseLinear_phaseDerivative]
    exact (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hf' : HasFDerivAt f L.toContinuousLinearMap p := by
    have hprod := hφ'.prodMk ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp p L.hasFDerivAt)
    have heq : (phaseLinear (phaseDerivative φ p)).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap) = L.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq] at hprod
    exact hprod
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := {x : Base | IsUnit (fderiv ℝ f x)}
  have hW : IsOpen W := Units.isOpen.preimage (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hpW : p ∈ W := by
    change IsUnit (fderiv ℝ f p)
    rw [hf'.fderiv]
    exact L.toUnit.isUnit
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = f := rfl
  refine ⟨e,?_,?_,?_,?_⟩
  · exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hpW⟩
  · exact fun x => rfl
  · simpa only [he] using hf
  · intro y hy
    have hunit : IsUnit (fderiv ℝ f (e.symm y)) := (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := ContinuousLinearEquiv.ofUnit u
    have hd : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hf.differentiable (by simp) (e.symm y)).hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      exact hu
    exact (e.contDiffAt_symm hy hd (by rw [he]; exact hf.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ExtendedPhaseChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth extensions of local phase coordinates on smaller neighborhoods. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

/-- Shrinking a smooth local chart lets its inverse be represented by an
actual globally smooth function, as needed by the supported mode solver. -/
theorem extend_local_chart_inverse (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {p : Base} (hp : p ∈ e.source) :
    ∃ d : OpenPartialHomeomorph Base Base, p ∈ d.source ∧
      (d : Base → Base) = e ∧ d.source ⊆ e.source ∧ d.target ⊆ e.target ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm := by
  obtain ⟨B,hB,_,_,hEq⟩ := smooth_extension_near e.open_target hi.contMDiffOn (e.map_source hp)
  have hN : {y : Base | B y = e.symm y} ∩ e.target ∈ 𝓝 (e p) :=
    inter_mem hEq (e.open_target.mem_nhds (e.map_source hp))
  obtain ⟨V,hV,hVo,hVp⟩ := mem_nhds_iff.mp hN
  have hvEq {y : Base} (hy : y ∈ V) : B y = e.symm y := (hV hy).1
  let d : OpenPartialHomeomorph Base Base := {
    toFun := e
    invFun := B
    source := e.source ∩ e ⁻¹' V
    target := e.target ∩ V
    map_source' := fun x hx => ⟨e.map_source hx.1,hx.2⟩
    map_target' := by
      intro y hy
      rw [hvEq hy.2]
      refine ⟨e.map_target hy.1,?_⟩
      change e (e.symm y) ∈ V
      simpa only [e.right_inv hy.1] using hy.2
    left_inv' := by
      intro x hx
      rw [hvEq hx.2]
      exact e.left_inv hx.1
    right_inv' := by
      intro y hy
      rw [hvEq hy.2]
      exact e.right_inv hy.1
    open_source := e.open_source.inter (hVo.preimage he.continuous)
    open_target := e.open_target.inter hVo
    continuousOn_toFun := he.continuous.continuousOn
    continuousOn_invFun := hB.contDiff.continuous.continuousOn
  }
  exact ⟨d,⟨hp,hVp⟩,rfl,fun _ h => h.1,fun _ h => h.1,he,hB.contDiff⟩

/-- Every noncritical phase admits the globally smooth representatives used
by local polynomial cancellation. This is a geometric construction. -/
theorem exists_extended_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm := by
  obtain ⟨e,hep,hphase,he,hi⟩ := exists_smooth_phase_chart hφ hp
  obtain ⟨d,hdp,hde,_,_,hd,hdi⟩ := extend_local_chart_inverse e he hi hep
  exact ⟨d,hdp,fun x => by rw [hde]; exact hphase x,hd,hdi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good phase directions remain good in their actual nonlinear phase charts. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phaseDerivative_comp_smooth {φ : Base → ℝ} {f : Base → Base}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (p : Base) :
    phaseDerivative (φ ∘ f) p = pullCovector (fderiv ℝ f p) (phaseDerivative φ (f p)) := by
  unfold phaseDerivative
  rw [fderiv_comp p (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)]
  change ((fderiv ℝ φ (f p)) ((fderiv ℝ f p) dx),
    (fderiv ℝ φ (f p)) ((fderiv ℝ f p) dy)) = _
  conv_lhs => rw [← phaseLinear_phaseDerivative φ (f p)]
  rfl

lemma inverse_chart_derivative (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ Base := by
  have hh : e ∘ e.symm =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [← fderiv_comp y (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
    hh.fderiv_eq,fderiv_id]

lemma inverse_chart_derivative_injective (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    Function.Injective (fderiv ℝ e.symm y) := by
  have hh := inverse_chart_derivative e he hi hy
  intro u v huv
  have h := congrArg (fderiv ℝ e (e.symm y)) huv
  change ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) u =
    ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) v at h
  simpa only [hh,ContinuousLinearMap.id_apply] using h

lemma inverse_chart_phase_covector {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = φ x) {y : Base} (hy : y ∈ e.target) :
    pullCovector (fderiv ℝ e.symm y) (phaseDerivative φ (e.symm y)) = dx := by
  have hh : φ ∘ e.symm =ᶠ[𝓝 y] Prod.fst := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    change φ (e.symm z) = z.1
    rw [← hphase,e.right_inv hz]
  rw [← phaseDerivative_comp_smooth hφ hi]
  unfold phaseDerivative
  rw [hh.fderiv_eq,fderiv_fst]
  rfl

/-- A nonlinear first-coordinate chart carries precisely the good direction
needed by the local free and forced mode constructions. -/
theorem realModeDomain_smooth_phase_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = φ x)
    (hImm : ∀ x ∈ e.source, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ e.source, Good (realSecondTensor F x) (phaseDerivative φ x)) :
    RealModeDomain (F ∘ e.symm) e.target := by
  refine ⟨e.open_target,?_,?_⟩
  · intro y hy
    apply gramDet_ne_zero_of_injective
    rw [fderiv_comp y (hF.differentiable (by simp) _) (hi.differentiable (by simp) _)]
    exact (hImm _ (e.map_target hy)).comp (inverse_chart_derivative_injective e he hi hy)
  · intro y hy
    have hD := gramDet_ne_zero_of_injective (fderiv ℝ F (e.symm y)) (hImm _ (e.map_target hy))
    have hdet : coordDet (fderiv ℝ e.symm y) ≠ 0 :=
      coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source
        hi.contDiffOn he.contDiffOn (fun _ hz => e.map_target hz) (fun z hz => e.right_inv hz) hy
    have hq := phase_length_comp_smooth hF hi (phaseDerivative φ (e.symm y)) y hD hdet
    rw [inverse_chart_phase_covector hφ e hi hphase hy] at hq
    have hn : secondQuadratic (realSecondTensor (F ∘ e.symm) y) dy ≠ 0 := by
      simp only [dx,neg_zero] at hq
      change secondQuadratic (realSecondTensor (F ∘ e.symm) y) (0,1) ≠ 0
      rw [hq]
      exact smul_ne_zero (pow_ne_zero 2 hdet) (hgood _ (e.map_target hy)).2
    change realSecondForm (F ∘ e.symm) dy dy y ≠ 0
    rw [realSecondForm_quadratic (hF.comp hi)]
    exact hn

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly contained local domains for actual noncritical good phases. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

/-- A good phase at an immersed point has an actual smaller phase chart with
compact source and target bounds inside a larger good-mode domain. -/
theorem exists_good_phase_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : Base}
    (hImm : Function.Injective (fderiv ℝ F p))
    (hgood : Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ (d : OpenPartialHomeomorph Base Base) (KE KV Ω : Set Base),
      p ∈ d.source ∧ (∀ x, (d x).1 = φ x) ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm ∧
      IsCompact KE ∧ IsCompact KV ∧ d.source ⊆ KE ∧ d.target ⊆ KV ∧ KV ⊆ Ω ∧
      RealModeDomain (F ∘ d.symm) Ω := by
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ F p) hImm
  have hde : ∀ᶠ x in 𝓝 p,
      NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0 :=
    (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  have hge := good_eventually (contDiffAt_realSecondTensor hF p hD).continuousAt
    (continuous_phaseDerivative hφ).continuousAt hgood
  obtain ⟨U,hUs,hU,hpU⟩ := mem_nhds_iff.mp (hde.and hge)
  obtain ⟨e₀,hep,hphase,he₀,hi₀⟩ := exists_extended_phase_chart hφ hgood.1
  let e := e₀.restrOpen U hU
  have hep' : p ∈ e.source := ⟨hep,hpU⟩
  have he : ContDiff ℝ ∞ e := he₀
  have hi : ContDiff ℝ ∞ e.symm := hi₀
  have hdom : RealModeDomain (F ∘ e.symm) e.target :=
    realModeDomain_smooth_phase_chart hF hφ e he hi hphase
      (fun x hx => injective_of_gramDet_ne_zero _ (hUs hx.2).1)
      (fun x hx => (hUs hx.2).2)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_source p hep'
  let V := Metric.ball p (r/2)
  let KE := Metric.closedBall p (r/2)
  have hKE : IsCompact KE := isCompact_closedBall p (r/2)
  have hKEe : KE ⊆ e.source :=
    (Metric.closedBall_subset_ball (by linarith : r/2 < r)).trans hball
  let d := e.restrOpen V Metric.isOpen_ball
  let KV := e '' KE
  have hKV : IsCompact KV := hKE.image he.continuous
  refine ⟨d,KE,KV,e.target,?_,hphase,he,hi,hKE,hKV,?_,?_,?_,hdom⟩
  · exact ⟨hep',Metric.mem_ball_self (by linarith)⟩
  · intro x hx
    exact Metric.ball_subset_closedBall hx.2
  · intro y hy
    refine ⟨d.symm y,?_,?_⟩
    · exact Metric.ball_subset_closedBall (d.map_target hy).2
    · exact d.right_inv hy
  · rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKEe hx)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseCover
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite good phase charts covering the compact support of a correction. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

theorem exists_goodPhaseChart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : Base}
    (hImm : Function.Injective (fderiv ℝ F p))
    (hgood : Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ c : GoodPhaseChart F φ, p ∈ c.chart.source := by
  obtain ⟨d,KE,KV,Ω,hp,hphase,he,hi,hKE,hKV,hsource,htarget,hinside,hdom⟩ :=
    exists_good_phase_neighborhood hF hφ hImm hgood
  exact ⟨⟨d,hphase,he,hi,⟨KE,hKE⟩,⟨KV,hKV⟩,Ω,hsource,htarget,hinside,hdom⟩,hp⟩

/-- No global coordinate chart for a mixed phase is assumed: finitely many
actual local phase charts cover its compact support. -/
theorem finite_good_phase_cover {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
    (hImm : ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ (K : Set Base), Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ (t : Finset K) (c : t → GoodPhaseChart F φ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source := by
  classical
  choose c hc using fun p : K => exists_goodPhaseChart hF hφ (hImm p p.property) (hgood p p.property)
  have hcover : (K : Set Base) ⊆ ⋃ p : K, (c p).chart.source := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hc ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := K.isCompact.elim_finite_subcover (fun p : K => (c p).chart.source)
    (fun p => (c p).chart.open_source) hcover
  refine ⟨t,fun i => c i.val,?_⟩
  intro p hp
  obtain ⟨i,hit,hi⟩ := mem_iUnion₂.mp (ht hp)
  exact mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed local good-phase charts persist under a global C2 perturbation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F-G) = A.vectorPlaneRead i F - A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseSupportCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer compact phase supports between the two plane coordinate conventions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma onModeSupport_seminorm (K : Compacts SmallModes.Base) (s : ℝ≥0)
    (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := E) K) :
    supportedWeightedSeminorm (modeSupport (jetSupport K)) s m (onModeSupport K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      (onModeSupport K f) (weightedBound_of_supportedSeminorm s m f)
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      f (weightedBound_of_supportedSeminorm s m (onModeSupport K f))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhasePartition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite smooth partitions on the compact set on which a phase correction is
required.  The coefficients have compact support inside the supplied open
phase domains.  These are ordinary partition coefficients, so splitting a
tensor target does not require taking square roots.
-/

noncomputable section

open Set Manifold TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)

/-- A finite open cover of a compact subset of the phase plane admits compactly
supported smooth partition coefficients indexed by that same cover. -/
theorem exists_compact_phase_partition {ι : Type*} [Fintype ι]
    {K : Set Base} (hK : IsCompact K) (U : ι → Set Base)
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    Nonempty (CompactPhasePartition ι K U) := by
  classical
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Base)
  let V : ι → Set Base := fun i => U i ∩ Metric.ball 0 r
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).inter Metric.isOpen_ball
  have hcoverV : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, hi, hr hx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Base))
    hK.isClosed V hV hcoverV
  refine ⟨{
    weight := fun i => ρ i
    smooth := fun i => (ρ i).contMDiff.contDiff
    nonneg := ρ.nonneg
    le_one := ρ.le_one
    compact_support := ?_
    subordinate := fun i x hx => (hρ i hx).1
    sum_eq_one := ?_ }⟩
  · intro i
    apply (isCompact_closedBall (0 : Base) r).of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    exact Metric.ball_subset_closedBall ((hρ i hx).2)
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedTarget
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Split an actual smooth compactly supported target using the finite smooth
phase partition.  Every piece is a supported smooth field on a compact subset
of its phase domain, and the sum of the pieces is the original target.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pieceSupport_subset_original (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) ⊆ K := fun _ hx => hx.1

/-- The finite pieces sum to the original target at every point, including
outside the compact set on which the coefficients sum to one. -/
theorem sum_splitSupported_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (x : Base) :
    ∑ i, P.splitSupported A i x = A x := by
  classical
  simp only [splitSupported_apply, ← Finset.sum_smul]
  by_cases hx : x ∈ (K : Set Base)
  · rw [P.sum_eq_one x hx, one_smul]
  · simp only [A.zero_on_compl hx, Pi.zero_apply, smul_zero]

end CompactPhasePartition

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-order bounds for the actual partition split.  A fixed partition has
bounded derivatives of every fixed order.  Consequently the split costs a
constant depending only on that partition and the order, uniformly over all
short scales at most one and linearly in the target seminorm.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

open SmallModes (Base)
open JetPolynomial (SupportedField supportedWeightedSeminorm
  weightedBound_of_supportedSeminorm supportedSeminorm_le_of_weightedBound)
open WeightedEstimates

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

theorem weightSize_nonneg (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) (i : ι) :
    0 ≤ P.weightSize m i := apply_nonneg _ _

theorem weight_weightedBound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : (s : ℝ) ≤ 1) :
    WeightedBound univ s m (P.weightSize m i) (P.weight i) := by
  exact (weightedBound_of_supportedSeminorm (1 : ℝ≥0) m
    (P.supportedWeight i)).shrink_scale s.coe_nonneg hs

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product estimate with the coefficient's explicit derivative size. -/
theorem splitSupported_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      (2 ^ m * P.weightSize m i) * supportedWeightedSeminorm K s m A := by
  have hA := weightedBound_of_supportedSeminorm s m A
  have hprod := (P.weight_weightedBound m i s hs1).smul_real uniqueDiffOn_univ
    s.coe_nonneg (P.weightSize_nonneg m i) (apply_nonneg _ _)
    (P.smooth i).contDiffOn A.contDiff.contDiffOn hA
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (mul_nonneg (by positivity) (P.weightSize_nonneg m i))
      (apply_nonneg _ _)) (P.splitSupported A i) hprod

theorem one_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) :
    1 ≤ P.splitConstant m := by
  have hsum : 0 ≤ ∑ i, 2 ^ m * P.weightSize m i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (P.weightSize_nonneg m i))
  change 1 ≤ 1 + ∑ i, 2 ^ m * P.weightSize m i
  linarith

theorem coefficient_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) : 2 ^ m * P.weightSize m i ≤ P.splitConstant m := by
  classical
  have hi : 2 ^ m * P.weightSize m i ≤ ∑ j, 2 ^ m * P.weightSize m j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (P.weightSize_nonneg m j))
      (Finset.mem_univ i)
  change 2 ^ m * P.weightSize m i ≤ 1 + ∑ j, 2 ^ m * P.weightSize m j
  linarith

/-- The fixed finite partition costs no negative power of the scale. -/
theorem splitSupported_uniform_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      P.splitConstant m * supportedWeightedSeminorm K s m A :=
  (P.splitSupported_bound m i s hs hs1 A).trans
    (mul_le_mul_of_nonneg_right (P.coefficient_le_splitConstant m i) (apply_nonneg _ _))

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the geometric charts when constructing the compact target split. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem exists_compactPhaseFamily
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p)) : Nonempty (CompactPhaseFamily F φ K) := by
  obtain ⟨t,e,hcover⟩ := finite_good_phase_cover
    (hF.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) K hImm hgood
  obtain ⟨P⟩ := PhasePartitions.exists_compact_phase_partition K.isCompact
    (fun i : t => (e i).chart.source) (fun i => (e i).chart.open_source) hcover
  exact ⟨⟨t,e,P⟩⟩

namespace CompactPhaseFamily
variable {F : JetPolynomial.Base → JetPolynomial.Space} {φ : JetPolynomial.Base → ℝ}
  {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)

lemma support_subset (i : a.centers) : (modeSupport (a.support i) : Set SmallModes.Base) ⊆ K := by
  simpa only [support,modeSupport_jetSupport] using a.partition.pieceSupport_subset_original i

lemma split_sum (f : SupportedField (F := ComplexTensor) K) (x : SmallModes.Base) :
    ∑ i, a.split i f x = f x := a.partition.sum_splitSupported_apply f x

lemma split_bound (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (m : ℕ) (i : a.centers) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (modeSupport (a.support i)) s m (a.split i f) ≤
      a.partition.splitConstant m * supportedWeightedSeminorm K s m f := by
  change supportedWeightedSeminorm (modeSupport (jetSupport (a.partition.pieceSupport i))) s m
    (onModeSupport (a.partition.pieceSupport i) (a.partition.splitSupported f i)) ≤ _
  rw [onModeSupport_seminorm _ s hs]
  exact a.partition.splitSupported_uniform_bound m i s hs hs1 f

end CompactPhaseFamily
end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialProfileTransfer
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The size and residual factors depend only on numeric coefficient profiles,
not on the map, phase, chart, target or scale in a solver record.  The pure
profiles let a family use those factors without introducing a reference
solver at unit scale.
-/

noncomputable section

open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ}

theorem κProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (m : ℕ) : 0 ≤ κProfile P C D m :=
  (SmallModes.errorConstant_nonneg m (hC m)).trans (le_max_left _ _)

theorem sizeProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 0 ≤ J m) (q m : ℕ) :
    0 ≤ sizeProfile P C D J q m :=
  mul_nonneg (mul_nonneg (by positivity)
    (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) C D hC q m))
    (pow_nonneg (hJ m) _)

theorem residualProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 0 ≤ J m) (q m : ℕ) :
    0 ≤ residualProfile P C D J q m :=
  mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m (hJ m) (hJ (m + 1))) (by positivity))
    (FiniteParametrix.boundProfile_nonneg (κProfile_nonneg P C D hC)
      (κProfile_nonneg P C D hC) q m)

variable {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem κ_eq_κProfile {C D : ℕ → ℝ} (hC : c.C = C) (hD : c.D = D) :
    c.κ = κProfile P C D := by
  funext m
  simp only [κ, κProfile, hC, hD]

theorem sizeFactor_eq_sizeProfile {C D J : ℕ → ℝ}
    (hC : c.C = C) (hD : c.D = D) (hJ : c.J = J) (q m : ℕ) :
    c.sizeFactor q m = sizeProfile P C D J q m := by
  simp only [sizeFactor, sizeProfile, hC, hD, hJ]

theorem residualFactor_eq_residualProfile {C D J : ℕ → ℝ}
    (hC : c.C = C) (hD : c.D = D) (hJ : c.J = J) (q m : ℕ) :
    c.residualFactor q m = residualProfile P C D J q m := by
  simp only [residualFactor, residualProfile, hJ, c.κ_eq_κProfile hC hD]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInputNorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual tensor input norm of the phase solver. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

theorem norm_le_of_weightedBound (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (I : ℕ → ℝ) (hI : ∀ m, 1 ≤ I m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ c.e.target,
      ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I m)
    (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (f : SupportedField (F := ComplexTensor) (modeSupport K))
    (hb : WeightedBound Set.univ s m C f) :
    c.norm f m ≤ tensorChartBudget m (I m) (I (m + 1)) * C := by
  have hn := supportedSeminorm_le_of_weightedBound hs hC f hb
  have hfield := RealModes.weighted_coordDeriv_of_jets c.e.open_target c.smoothInverse s.coe_nonneg hs1
    (zero_le_one.trans (hI (m + 1))) (hcoords (m + 1))
  have hh := tensorChartPush_bound c.e (modeSupport K) c.supportChart c.smoothInverse hs hs1
    (hI m) (zero_le_one.trans (hI (m + 1))) (hcoords m) hfield f
  exact hh.trans (mul_le_mul_of_nonneg_left hn
    (tensorChartBudget_nonneg m (zero_le_one.trans (hI m)) (zero_le_one.trans (hI (m + 1)))))

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DisplacementSum
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recombination of phase targets split by a finite partition. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.QuadraticMean

lemma realMode_sum {n : ℕ} {ι : Type*} [Fintype ι] (θ : ℝ) (A : ι → CVec n) :
    realMode θ (∑ i, A i) = ∑ i, realMode θ (A i) := by
  funext k
  simp [realMode,realPart,Finset.mul_sum]

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialProfiledSplitCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite cancellation from actual-scale solver records with fixed
numeric profiles.  No reference solver at unit scale is used.  All constants
are selected before the map, phase, target and both scales.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal

namespace ClosedSurfaceR4.PhaseGeometry

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem polynomial_profiled_split_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (K : Compacts SmallModes.Base)
    (L : ι → Compacts JetPolynomial.Base)
    (T : (i : ι) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)))
    (hLK : ∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K)
    (C D J I : ι → ℕ → ℝ) (hC : ∀ i m, 0 ≤ C i m)
    (hJ : ∀ i m, 1 ≤ J i m) (hI : ∀ i m, 1 ≤ I i m)
    (S : ℕ → ℝ) (hS : ∀ m, 1 ≤ S m)
    (hT : ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ m i A,
      supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
        S m * supportedWeightedSeminorm K s m A)
    (hsum : ∀ A x, ∑ i, T i A x = A x) (q : ℕ) :
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (φ : JetPolynomial.Base → ℝ) (τ ε : ℝ) (s : ℝ≥0),
        0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → τ/s+ε/τ^tensorLoss P ≤ 1 →
      ∀ (c : (i : ι) → PolynomialSolveData P ε G hG φ (L i) τ s),
        (∀ i, (c i).C = C i) → (∀ i, (c i).D = D i) → (∀ i, (c i).J = J i) →
        (∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (Cv m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ / s + ε/τ^tensorLoss P) ^ (q + 1) * Ct m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A)
          (coordinateFullLinearized P ε G X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  let b : ι → ℕ → ℝ := fun i m =>
    tensorChartBudget m (I i m) (I i (m + 1)) * S m
  have hbn (i : ι) (m : ℕ) : 0 ≤ b i m :=
    mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans (hI i m))
      (zero_le_one.trans (hI i (m + 1)))) (zero_le_one.trans (hS m))
  let V : ι → ℕ → ℝ := fun i m =>
    PolynomialSolveData.sizeProfile P (C i) (D i) (J i) q m
  let R : ι → ℕ → ℝ := fun i m =>
    PolynomialSolveData.residualProfile P (C i) (D i) (J i) q m
  have hV (i : ι) (m : ℕ) : 0 ≤ V i m :=
    PolynomialSolveData.sizeProfile_nonneg P (C i) (D i) (J i) (hC i)
      (fun m => zero_le_one.trans (hJ i m)) q m
  have hR (i : ι) (m : ℕ) : 0 ≤ R i m :=
    PolynomialSolveData.residualProfile_nonneg P (C i) (D i) (J i) (hC i)
      (fun m => zero_le_one.trans (hJ i m)) q m
  let Cv := fun m => ∑ i, V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)
  let Ct := fun m => ∑ i, R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)
  refine ⟨Cv, Ct, ?_, ?_, ?_⟩
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hV i m) (hbn i _))
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hR i m) (hbn i _))
  · intro G hG φ τ ε s hτ hs hτs hs1 hε hsmall c hc hd hj hi A
    obtain ⟨X, hX, hsp, hb, hr⟩ := finite_polynomial_cancellation P ε hG
      (fun _ : ι => φ) L c hτ hs hτs hs1 hε hsmall (fun i => T i A) q
    have hn (i : ι) (m : ℕ) : (c i).norm (T i A) m ≤
        b i m * supportedWeightedSeminorm K s m A := by
      have hbound := (c i).norm_le_of_weightedBound hs hs1 (I i) (hI i) (hi i) m
        (mul_nonneg (zero_le_one.trans (hS m)) (apply_nonneg _ _)) (T i A)
        ((weightedBound_of_supportedSeminorm s m (T i A)).mono_const
          (hT s hs hs1 m i A))
      simpa only [b, mul_assoc] using hbound
    have hsz (i : ι) (m : ℕ) : (c i).size (T i A) q m ≤
        (V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).size_eq_factor, (c i).sizeFactor_eq_sizeProfile (hc i) (hd i) (hj i)]
      exact (mul_le_mul_of_nonneg_left (hn i _) (hV i m)).trans_eq (mul_assoc _ _ _).symm
    have hres (i : ι) (m : ℕ) : (c i).residual (T i A) q m ≤
        (τ / s + ε/τ^tensorLoss P) ^ (q + 1) * (R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).residual_eq_factor, (c i).residualFactor_eq_residualProfile (hc i) (hd i) (hj i)]
      calc
        _ ≤ ((τ / s + ε/τ^tensorLoss P) ^ (q + 1) * R i m) *
            (b i (PolynomialSolveData.inputOrder (P := P) q m) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A) :=
          mul_le_mul_of_nonneg_left (hn i _)
            (mul_nonneg (pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _) (hR i m))
        _ = _ := by ring
    have hdisp (x : SmallModes.Base) :
        ∑ i, QuadraticMean.displacement τ (coordinatePhase φ) (T i A) x =
          QuadraticMean.displacement τ (coordinatePhase φ) A x := by
      simp only [QuadraticMean.displacement]
      rw [← QuadraticMean.realMode_sum, hsum A x]
    refine ⟨X, hX, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsp hx)
      exact hLK i hi
    · intro m
      apply (hb m).mono_const
      calc
        _ ≤ ∑ i, (V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
          Finset.sum_le_sum (fun i _ => hsz i m)
        _ = _ := (Finset.sum_mul _ _ _).symm
    · intro m
      have hbound : (∑ i, (c i).residual (T i A) q m) ≤
          (τ / s + ε/τ^tensorLoss P) ^ (q + 1) * Ct m *
            supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
        calc
          _ ≤ ∑ i, (τ / s + ε/τ^tensorLoss P) ^ (q + 1) *
              (R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
            Finset.sum_le_sum (fun i _ => hres i m)
          _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      simpa only [hdisp, Pi.add_def] using
        (hr m).mono_const hbound

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformPolynomialNearbyCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial cancellation on compact supports, uniform over nearby maps. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem uniform_polynomial_nearby_cancellation_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ x ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x))
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
    (hUK : U ⊆ KU) (hKU : (jetSupport K : Set JetPolynomial.Base) ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G) (B : ℝ),
      0 ≤ B → B < ρ → WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^tensorLoss P ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m (Cv m * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := P) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m ((τ/s+ε/τ^tensorLoss P)^(q+1)*Ct m *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A)
          (coordinateFullLinearized P ε G X+QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  obtain ⟨a⟩ := exists_compactPhaseFamily hF hφ K hImm hgood
  obtain ⟨ρ,hρ,hall⟩ := a.uniform_polynomial_solvers_all_profiles P hP hF hφ hU KU hUK hKU
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  obtain ⟨C,D,J,I,hC,_,hJ,hI,hsol⟩ := hall R hR
  obtain ⟨Cv,Ct,hCv,hCt,hcancel⟩ := polynomial_profiled_split_cancellation P K
    a.support a.split a.support_subset C D J I hC hJ hI a.partition.splitConstant
    a.partition.one_le_splitConstant a.split_bound a.split_sum q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hsmall hp A
  obtain ⟨c,hc,hd,hj,hi⟩ := hsol G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hp
  exact hcancel G hG φ τ ε s hτ hs hτs hs1 hε hsmall c hc hd hj hi A

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialNearbyCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Atlas cancellation uniform over a neighborhood of a fixed immersion.
The reference geometry, per-chart shifted profiles and finite phase family
determine all constants before the varying map, target or scale is chosen.
-/

noncomputable section

open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nearbyPhasePolynomialDualAdd
local instance nearbyPhasePolynomialFiberNormed_r95c9e6_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance nearbyPhasePolynomialFiberSpace_r95c9e6_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance nearbyPhasePolynomialDualSmul_r95c9e6_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance nearbyPhasePolynomialSectionNormed_r95c9e6_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nearbyPhasePolynomialSectionSpace_r95c9e6_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Fixed good-phase geometry gives uniform global cancellation for nearby
maps with the specified shifted derivative profiles at the actual slow scale. -/
theorem atlas_polynomial_nearby_cancellation_all_profiles
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {nq : ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrepr : A.PolynomialLinearRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (hImm : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) p))
    (hgood : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) p)
        (phaseDerivative (coordinatePhase (φ i j)) p))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i) (hKU : ∀ i j, (K i j : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : (i : A.centers) → ι i → ℝ, (∀ i j, 0 < ρ i j) ∧
      ∀ (R : A.centers → ℕ → ℝ), (∀ i m, 0 ≤ R i m) → ∀ q : ℕ,
      ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
      (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G)
        (B : (i : A.centers) → ι i → ℝ),
        (∀ i j, 0 ≤ B i j) → (∀ i j, B i j < ρ i j) →
        (∀ i j, WeightedEstimates.WeightedBound univ 1 2 (B i j)
          ((spaceCoordinates ∘ A.vectorPlaneRead i G) -
            (spaceCoordinates ∘ A.vectorPlaneRead i F))) →
      ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
        (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ i m l, l ≤ m + 2 → WeightedEstimates.WeightedBound univ 1 l
          (R i m / (s : ℝ) ^ (l - 2)) (spaceCoordinates ∘ A.vectorPlaneRead i G)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (η ^ (q + 1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation P ε G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  have hlocal (i : A.centers) (j : ι i) :=
    PhaseGeometry.uniform_polynomial_nearby_cancellation_all_profiles (Q i) (hQ i) (A.jetChartMap_smooth i hF)
      (hφ i j) (modeSupport (K i j))
      (by simpa only [A.jetChartMap_plane] using hImm i j)
      (by simpa only [A.jetChartMap_plane] using hgood i j)
      (hU i) (KU i) (hUK i) (by
        rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa only [planeCoordinateIsometry.symm_apply_apply] using hKU i j hz)
  choose ρ hρ hall using hlocal
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  choose Cv Ct hCv hCt solve using fun i j => hall i j (R i) (hR i) q
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.tensorPlaneRestore_bound m
  refine ⟨fun i j m => Dv m * Cv i j m, fun i j m => Dt m * Ct i j m,
    fun i j m => mul_nonneg (hDv m) (hCv i j m),
    fun i j m => mul_nonneg (hDt m) (hCt i j m), ?_⟩
  intro G hG B hB hBρ hnear τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hprefix target
  choose X hX hsp hb hr using fun i j => solve i j (A.jetChartMap i G)
    (A.jetChartMap_smooth i hG) (B i j) (hB i j) (hBρ i j)
    (by simpa only [A.jetChartMap_plane] using hnear i j) τ ε s hτ hs hτs hs1 hε hε1 ((hsmall i).trans hη1)
    (by simpa only [A.jetChartMap_plane] using hprefix i) (target i j)
  let Y : A.centers → RealModes.RField 4 := fun i x => ∑ j, X i j x
  have hY (i : A.centers) : ContDiff ℝ ∞ (Y i) :=
    ContDiff.sum (fun j _ => hX i j)
  have hYs (i : A.centers) : tsupport (Y i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    apply closure_minimal _ (modeSupport (A.chartWeightCompact i)).isCompact.isClosed
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    exact image_eq_zero_of_notMem_tsupport (fun hxj => hn (hK i j (hsp i j hxj)))
  let T : A.centers → SmallModes.Base → Tensor := fun i x => ∑ j,
    QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x
  have hd (i : A.centers) (j : ι i) : ContDiff ℝ ∞
      (QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j)) :=
    contDiffOn_univ.mp (RealModes.contDiffOn_displacement
      ((hφ i j).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      (target i j).contDiff.contDiffOn τ)
  have hT (i : A.centers) : ContDiff ℝ ∞ (T i) := ContDiff.sum (fun j _ => hd i j)
  let v : A.centers → ℕ → ℝ := fun i m => ∑ j, Cv i j m *
    supportedWeightedSeminorm (modeSupport (K i j)) s
      (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)
  let t : A.centers → ℕ → ℝ := fun i m => ∑ j, Ct i j m *
    supportedWeightedSeminorm (modeSupport (K i j)) s
      (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)
  have hvn (i : A.centers) (m : ℕ) : 0 ≤ v i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCv i j m) (apply_nonneg _ _))
  have htn (i : A.centers) (m : ℕ) : 0 ≤ t i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCt i j m) (apply_nonneg _ _))
  have hsize (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m (v i m) (Y i) :=
    WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ _ _
      (fun j _ => (hX i j).contDiffOn) (fun j _ => hb i j m)
  have hlin (i : A.centers) :
      coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) =
        fun x => ∑ j, coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) x := by
    exact coordinateFullLinearized_sum (Q i) ε (A.jetChartMap i G)
        Finset.univ (X i) (hX i)
  have hres (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m
      (η ^ (q + 1) * t i m)
      (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) + T i) := by
    have he : (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) + T i) =
        fun x => ∑ j, (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) x +
            QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x) := by
      funext x
      rw [Pi.add_apply, hlin]
      exact Finset.sum_add_distrib.symm
    rw [he]
    have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun j => η ^ (q + 1) * Ct i j m *
        supportedWeightedSeminorm (modeSupport (K i j)) s
          (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
      (fun j => coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) +
        QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j))
      (fun j _ => (coordinateFullLinearized_smooth isOpen_univ isOpen_univ (Q i) (hQ i)
        (A.jetChartMap_smooth i hG) (fun _ _ => mem_univ _) (A.chartWeightCompact i)
        (subset_univ _) (hX i j) ((hsp i j).trans (hK i j)) ε).contDiffOn.add (hd i j).contDiffOn)
      (fun j _ => (hr i j m).mono_const (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _)))
          (hsmall i) (q+1)) (hCt i j m)) (apply_nonneg _ _)))
    simpa only [t, Finset.mul_sum, mul_assoc, Pi.add_apply] using hsum
  refine ⟨A.vectorPlaneRestore Y, A.vectorPlaneRestore_smooth Y hY, ?_, ?_⟩
  · intro m
    have hh := hv m Y τ (∑ i, v i m) hτ (hτs.trans hs1)
      (Finset.sum_nonneg (fun i _ => hvn i m)) hY
      (fun i => (hsize i m).mono_const
        (Finset.single_le_sum (fun k _ => hvn k m) (Finset.mem_univ i)))
    simpa only [v, Finset.mul_sum, mul_assoc] using hh
  · intro m
    have hηpow : 0 ≤ η ^ (q + 1) := pow_nonneg hη _
    rw [hrepr G hG Y hY hYs ε, ← A.tensorPlaneRestore_add]
    have hh := ht m (fun i => coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i)+T i)
      τ (η^(q+1) * ∑ i, t i m) hτ (hτs.trans hs1)
      (mul_nonneg hηpow (Finset.sum_nonneg (fun i _ => htn i m)))
      (fun i => (coordinateFullLinearized_smooth isOpen_univ isOpen_univ (Q i) (hQ i)
        (A.jetChartMap_smooth i hG) (fun _ _ => mem_univ _) (A.chartWeightCompact i)
        (subset_univ _) (hY i) (hYs i) ε).add (hT i))
      (fun i => (hres i m).mono_const (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => htn k m) (Finset.mem_univ i)) hηpow))
    have he : Dt m * (η^(q+1) * ∑ i, t i m) =
        η^(q+1) * ∑ i : A.centers, ∑ j, (Dt m * Ct i j m) *
          supportedWeightedSeminorm (modeSupport (K i j)) s
            (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j) := by
      calc
        _ = η^(q+1) * (Dt m * ∑ i, t i m) := by ring
        _ = _ := by simp only [t, Finset.mul_sum, mul_assoc]
    rw [he] at hh
    exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialInputCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform atlas cancellation from the global norms used in the iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPhasePolynomialDualAdd
local instance inputPhasePolynomialFiberNormed_r95c9e6_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPhasePolynomialFiberSpace_r95c9e6_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance inputPhasePolynomialDualSmul_r95c9e6_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance inputPhasePolynomialSectionNormed_r95c9e6_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPhasePolynomialSectionSpace_r95c9e6_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_input_cancellation_all_profiles_oai
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrepr : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (hImm : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) p))
    (hgood : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) p)
        (phaseDerivative (coordinatePhase (φ i j)) p))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i) (hKU : ∀ i j, (K i j : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
    ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
      (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
        (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (η^(q+1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  choose E hE he using fun (i : A.centers) m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose E₀ hE₀ he₀ using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  obtain ⟨r,hr,hall⟩ := A.atlas_polynomial_nearby_cancellation_all_profiles Pol Q hQ hrepr F hF φ hφ K hK
    hImm hgood U hU KU hUK hKU
  have hL₀ (i) : 0 ≤ L*E₀ i := mul_nonneg (norm_nonneg _) (hE₀ i)
  obtain ⟨ρ,hρ,_,hρr⟩ := finite_positive_threshold
    (fun a : (i : A.centers) × ι i => r a.1 a.2/(1+L*E₀ a.1))
    (fun a => div_pos (hr a.1 a.2) (by linarith [hL₀ a.1]))
  refine ⟨ρ,hρ,?_⟩
  intro P hP q
  let R := fun i m => L*E i m*P m
  have hR (i m) : 0 ≤ R i m := mul_nonneg (mul_nonneg (norm_nonneg _) (hE i m)) (hP m)
  obtain ⟨C,D,hC,hD,hsolve⟩ := hall R hR q
  refine ⟨C,D,hC,hD,?_⟩
  intro G hG B hB hBρ hb τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hp target
  have hbnd (i j) : L*E₀ i*B < r i j := by
    have hh := (lt_div_iff₀ (show 0 < 1+L*E₀ i by linarith [hL₀ i])).mp
      (hBρ.trans_le (hρr ⟨i,j⟩))
    nlinarith
  apply hsolve G hG (fun i _ => L*E₀ i*B)
    (fun i _ => mul_nonneg (hL₀ i) hB) hbnd _ τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall _ target
  · intro i _
    have hh := (he₀ i (G-F) 1 B zero_lt_one le_rfl hB (hG.sub hF) hb).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simp only [ContinuousLinearEquiv.coe_coe] at hh
    change WeightedEstimates.WeightedBound univ 1 2 _
      (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hh
    have hsub : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
        (spaceCoordinates ∘ A.vectorPlaneRead i G) -
          (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
      rw [A.vectorPlaneRead_sub]
      funext x
      exact map_sub spaceCoordinates _ _
    rw [hsub] at hh
    simpa only [L,mul_assoc] using hh
  · intro i m j hj
    have hh := (he i m G s (P m) hs hs1 (hP m) hG (hp m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simpa only [R,L,mul_assoc,mul_div_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles_oai.{u_1, u_2}
