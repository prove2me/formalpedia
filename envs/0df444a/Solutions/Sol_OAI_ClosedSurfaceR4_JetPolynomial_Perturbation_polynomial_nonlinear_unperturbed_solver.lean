-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:44.998116+00:00
-- url     : https://prove2.me/submissions/f1fe87d3-6eb1-4343-bfef-b17b7cebc1a6

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_RealModes_polynomial_inverse_chart_twoJet_bound

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

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)



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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
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
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_linearIsometry {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set E} (hU : UniqueDiffOn ℝ U) {f : E → X} (hf : ContDiffOn ℝ ∞ f U)
    {s C : ℝ} {m : ℕ} (hb : WeightedBound U s m C f) (A : X →ₗᵢ[ℝ] Y) :
    WeightedBound U s m C (A ∘ f) := by
  intro j hj p hp
  rw [A.norm_iteratedFDerivWithin_comp_left (hf p hp) hU hp
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  exact hb j hj p hp

end ClosedSurfaceR4.RealModes

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JetBounds
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
open ClosedSurfaceR4.WeightedEstimates




namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_scalarCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ scalarCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hX (i : Fin 5) := contDiffAt_liftX (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hY (i : Fin 5) := contDiffAt_liftY (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have hr (i : Fin 5) := contDiffAt_cdiv (contDiffAt_dot (hn i) (hn 4))
    (contDiffAt_dot (hn 4) (hn 4)) hb
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hX 2
  · exact hY 2
  · exact hX 3
  · exact hY 3
  · exact hX 4
  · exact hY 4
  · exact hr 2
  · exact hr 3

lemma contDiffAt_vectorCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ vectorCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have ht (a b : ℂ) := contDiffAt_tangentLift (h 0) (h 1)
    (ux := fun _ => a) (uy := fun _ => b) contDiffAt_const contDiffAt_const hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hn 2
  · exact hn 3
  · exact ht 1 0
  · exact ht 0 1
  · exact ((contDiffAt_dot (hn 4) (hn 4)).fun_inv hb).smul (hn 4)

lemma Domain.smoothCoefficients {V : Set (TwoJet n)} (h : Domain V) :
    ContDiffOn ℝ ∞ coefficients V := by
  intro J hJ
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiffAt_pi.mp (contDiffAt_scalarCoefficients (h.determinant J hJ) (h.good J hJ)) i
  | inr i =>
    exact contDiffAt_pi.mp
      (contDiffAt_pi.mp (contDiffAt_vectorCoefficients (h.determinant J hJ) (h.good J hJ)) i.1) i.2

end LowJet

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
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
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
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
open SmallModes PhaseGeometry Set Filter

lemma gramDet_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base) :
    NormalFrame.gramDet (coordDeriv dx (F ∘ φ) p) (coordDeriv dy (F ∘ φ) p) =
    ((fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1)^2 *
      NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) := by
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ]
  change NormalFrame.gramDet (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    gramDet_change_basis]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedReciprocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseSqrt
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for normalization by a positive square root. -/
noncomputable section
open Set Polynomial
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inverse_half (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) x‖ =
      ‖(descPochhammer ℝ j).eval (-1/2)‖*x^(-1/2-(j : ℝ)) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi hx,Real.iter_deriv_rpow_const]
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]

lemma inverse_half_power_bound {x K : ℝ} (hx : 0 < x) (hK : 1 ≤ K)
    (hi : x⁻¹ ≤ K) {j m : ℕ} (hj : j ≤ m) :
    x^(-1/2-(j : ℝ)) ≤ K^(m+1) := by
  have he : x^(-1/2-(j : ℝ)) = (x⁻¹)^((j : ℝ)+1/2) := by
    rw [← Real.rpow_neg_one x,← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  have hj0 : 0 ≤ (j : ℝ)+1/2 := by positivity
  calc
    (x⁻¹)^((j : ℝ)+1/2) ≤ K^((j : ℝ)+1/2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hi hj0
    _ ≤ K^((m+1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      push_cast
      linarith)
    _ = K^(m+1) := Real.rpow_natCast _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_inverse_sqrt (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s C K : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ K) → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
        (fun x => (Real.sqrt (f x))⁻¹) := by
  let D : ℝ := 1+∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖
  have hD : 1 ≤ D := by
    have hh : 0 ≤ ∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [D]
    linarith
  have hDj {j : ℕ} (hj : j ≤ m) : ‖(descPochhammer ℝ j).eval (-1/2)‖ ≤ D := by
    have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) =>
      norm_nonneg ((descPochhammer ℝ i).eval (-1/2))) (Finset.mem_range.mpr (by omega : j < m+1))
    dsimp only [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro U hU s C K f hs hC hK hf hpos hi hb
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) (f x)‖ ≤ D*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inverse_half j (hpos x hx)]
    exact mul_le_mul (hDj hj) (inverse_half_power_bound (hpos x hx) hK (hi x hx) hj)
      (Real.rpow_nonneg (hpos x hx).le _) (zero_le_one.trans hD)
  have hbound := hb.comp hU isOpen_Ioi.uniqueDiffOn hs hC (by positivity : 0 ≤ D*K^(m+1))
    hf hg hpos hd
  have hbound' : WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
      ((fun y : ℝ => y^(-1/2 : ℝ)) ∘ f) := by
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hbound'.congr
  intro x hx
  simp only [Function.comp_apply,Real.sqrt_eq_rpow]
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (hpos x hx).le]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedRealAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real scalar and vector products used in the quantitative normal formula. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real_dup2 {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x*g x) := by
  intro j hj x hx
  calc
    _ ≤ s^j*(∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*
        ‖iteratedFDerivWithin ℝ i f U x‖*‖iteratedFDerivWithin ℝ (j-i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2^j*C*D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma contDiffOn_dot_real {ι : Type*} [Fintype ι] {U : Set E} {f g : E → ι → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => dotProduct (f x) (g x)) U :=
  ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))

lemma WeightedBound.dot_real_dup1 {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → ι → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ)*(2^m*C*D))
      (fun x => dotProduct (f x) (g x)) := by
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2^m*C*D)
    (fun i x => f x i*g x i)
    (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))
    (fun i _ => (hbf.component hU hs hC hf i).mul_real_dup2 hU hs hC hD
      (contDiffOn_pi.mp hf i) (contDiffOn_pi.mp hg i) (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,dotProduct] using hh

lemma WeightedBound.smul_real_pi {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f : E → ℝ} {g : E → ι → ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x • g x) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hg i)
  · intro i
    exact hbf.mul_real_dup2 hU hs.le hC hD hf (contDiffOn_pi.mp hg i)
      (hbg.component hU hs.le hD hg i)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNormalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the Gram determinant, tangential
coefficients and normal projection. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dotBudget_nonneg (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ dotBudget m C := by
  unfold dotBudget
  positivity
lemma quadraticBudget_ge_one (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ quadraticBudget m C := by
  have hd := dotBudget_nonneg m hC
  unfold quadraticBudget
  have hh : 0 ≤ 2*(2^m*dotBudget m C*dotBudget m C) := by positivity
  linarith
lemma inverseGramBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ inverseGramBudget m C K := by
  have hd := (quadraticBudget_ge_one m hC).trans' zero_le_one
  unfold inverseGramBudget
  positivity
lemma liftBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ liftBudget m C K := by
  have hq := (quadraticBudget_ge_one m hC).trans' zero_le_one
  have hi := inverseGramBudget_nonneg m hC hK
  unfold liftBudget
  positivity

lemma weighted_quadratic_pair {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    {X Y Z W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bZ : WeightedBound U s m C Z) (bW : WeightedBound U s m C W) :
    WeightedBound U s m (quadraticBudget m C)
      (fun x => (X x ⬝ᵥ Y x)*(Z x ⬝ᵥ W x)-(X x ⬝ᵥ Z x)*(Y x ⬝ᵥ W x)) := by
  have hd := dotBudget_nonneg m hC
  have bd (A B : E → RVec 4) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
      (bA : WeightedBound U s m C A) (bB : WeightedBound U s m C B) :
      WeightedBound U s m (dotBudget m C) (fun x => A x ⬝ᵥ B x) :=
    bA.dot_real_dup1 hU hs hC hC hA hB bB
  have hleft := (bd X Y hX hY bX bY).mul_real_dup2 hU hs hd hd
    (contDiffOn_dot_real hX hY) (contDiffOn_dot_real hZ hW) (bd Z W hZ hW bZ bW)
  have hright := (bd X Z hX hZ bX bZ).mul_real_dup2 hU hs hd hd
    (contDiffOn_dot_real hX hZ) (contDiffOn_dot_real hY hW) (bd Y W hY hW bY bW)
  exact (hleft.sub hU hs
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hZ hW))
    ((contDiffOn_dot_real hX hZ).mul (contDiffOn_dot_real hY hW)) hright).mono_const (by
      unfold quadraticBudget
      linarith)

/-- Rational normal projection with an explicit polynomial dependence on
the inverse Gram bound. -/
theorem weighted_realNormalPart {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bW : WeightedBound U s m C W)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (normalBudget m C K) (fun x => realNormalPart (X x) (Y x) (W x)) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hquad := quadraticBudget_ge_one m hC0
  have hq0 := zero_le_one.trans hquad
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have bG : WeightedBound U s m (quadraticBudget m C)
      (fun x => NormalFrame.gramDet (X x) (Y x)) := by
    convert weighted_quadratic_pair hU hs.le hC0 hX hX hY hY bX bX bY bY using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    unfold NormalFrame.gramDet
    ring
  have bInv : WeightedBound U s m (inverseGramBudget m C K)
      (fun x => (NormalFrame.gramDet (X x) (Y x))⁻¹) :=
    bG.inv_real hU hs hquad hK hG hne hInv
  have hGI := hG.inv hne
  have bnX := weighted_quadratic_pair hU hs.le hC0 hY hY hX hW bY bY bX bW
  have bnY := weighted_quadratic_pair hU hs.le hC0 hX hX hY hW bX bX bY bW
  have hnX := ((contDiffOn_dot_real hY hY).mul (contDiffOn_dot_real hX hW)).sub
    ((contDiffOn_dot_real hY hX).mul (contDiffOn_dot_real hY hW))
  have hnY := ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hW)).sub
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hX hW))
  have bi := inverseGramBudget_nonneg m hC0 hK0
  have blX := bnX.mul_real_dup2 hU hs.le hq0 bi hnX hGI bInv
  have blY := bnY.mul_real_dup2 hU hs.le hq0 bi hnY hGI bInv
  have hlX := hnX.mul hGI
  have hlY := hnY.mul hGI
  have hbl := liftBudget_nonneg m hC0 hK0
  have btX := blX.smul_real_pi hU hs hbl hC0 hlX hX bX
  have btY := blY.smul_real_pi hU hs hbl hC0 hlY hY bY
  have hout := (bW.sub hU hs.le hW (hlX.smul hX) btX).sub hU hs.le
    (hW.sub (hlX.smul hX)) (hlY.smul hY) btY
  have hout' := hout.mono_const (show C+2^m*liftBudget m C K*C+2^m*liftBudget m C K*C ≤
      normalBudget m C K from by unfold normalBudget; ring_nf; rfl)
  apply hout'.congr
  intro x hx
  change realNormalPart (X x) (Y x) (W x) =
    W x-(((Y x ⬝ᵥ Y x)*(X x ⬝ᵥ W x)-(Y x ⬝ᵥ X x)*(Y x ⬝ᵥ W x))*
      (NormalFrame.gramDet (X x) (Y x))⁻¹) • X x-
      (((X x ⬝ᵥ X x)*(Y x ⬝ᵥ W x)-(X x ⬝ᵥ Y x)*(X x ⬝ᵥ W x))*
        (NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x
  simp only [realNormalPart,div_eq_mul_inv,dotProduct_comm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerpBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial derivative bounds for the perpendicular product and its
unit normalization used by the free mode. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma perpBudget_nonneg (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ perpBudget m C := by
  unfold perpBudget minorTermBudget crossBudget
  positivity

lemma weighted_minor3 {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bB : WeightedBound U s m C B) (i j k : Fin 4) :
    WeightedBound U s m (perpBudget m C) (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) := by
  have hy (a : Fin 4) := contDiffOn_pi.mp hY a
  have hb (a : Fin 4) := contDiffOn_pi.mp hB a
  have hx (a : Fin 4) := contDiffOn_pi.mp hX a
  have hcross (a b : Fin 4) := ((hy a).mul (hb b)).sub ((hy b).mul (hb a))
  have bcross (a b : Fin 4) : WeightedBound U s m (crossBudget m C)
      (fun x => Y x a*B x b-Y x b*B x a) := by
    have h₁ := (bY.component hU hs.le hC hY a).mul_real_dup2 hU hs.le hC hC (hy a) (hb b)
      (bB.component hU hs.le hC hB b)
    have h₂ := (bY.component hU hs.le hC hY b).mul_real_dup2 hU hs.le hC hC (hy b) (hb a)
      (bB.component hU hs.le hC hB a)
    convert h₁.sub hU hs.le ((hy a).mul (hb b)) ((hy b).mul (hb a)) h₂ using 1
    all_goals try with_reducible_and_instances rfl
    unfold crossBudget
    ring
  have hcb : 0 ≤ crossBudget m C := by unfold crossBudget; positivity
  have hterm (a b c : Fin 4) := (hx a).mul (hcross b c)
  have bterm (a b c : Fin 4) : WeightedBound U s m (minorTermBudget m C)
      (fun x => X x a*(Y x b*B x c-Y x c*B x b)) :=
    (bX.component hU hs.le hC hX a).mul_real_dup2 hU hs.le hC hcb (hx a) (hcross b c) (bcross b c)
  have ht := ((bterm i j k).sub hU hs.le (hterm i j k) (hterm j i k) (bterm j i k)).add
    hU hs.le ((hterm i j k).sub (hterm j i k)) (hterm k i j) (bterm k i j)
  convert ht using 1 <;> first | rfl | (unfold perpBudget; ring)

lemma contDiffOn_perpProduct {U : Set E} {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun x => NormalFrame.perpProduct (X x) (Y x) (B x)) U := by
  have hm (i j k : Fin 4) : ContDiffOn ℝ ∞
      (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) U := by
    unfold NormalFrame.minor3
    fun_prop
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hm 1 2 3).neg
  · exact hm 0 2 3
  · exact (hm 0 1 3).neg
  · exact hm 0 1 2

lemma weighted_perpProduct {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    {X Y B : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hB : ContDiffOn ℝ ∞ B U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bB : WeightedBound U s m C B) :
    WeightedBound U s m (perpBudget m C) (fun x => NormalFrame.perpProduct (X x) (Y x) (B x)) := by
  have hminor (i j k : Fin 4) : ContDiffOn ℝ ∞
      (fun x => NormalFrame.minor3 (X x) (Y x) (B x) i j k) U := by
    unfold NormalFrame.minor3
    fun_prop
  apply WeightedBound.pi hU hs (perpBudget_nonneg m hC)
  · intro i
    fin_cases i
    · exact (hminor 1 2 3).neg
    · exact hminor 0 2 3
    · exact (hminor 0 1 3).neg
    · exact hminor 0 1 2
  · intro i
    fin_cases i
    · exact (weighted_minor3 hU hs hC hX hY hB bX bY bB 1 2 3).neg hU (hminor 1 2 3)
    · exact weighted_minor3 hU hs hC hX hY hB bX bY bB 0 2 3
    · exact (weighted_minor3 hU hs hC hX hY hB bX bY bB 0 1 3).neg hU (hminor 0 1 3)
    · exact weighted_minor3 hU hs hC hX hY hB bX bY bB 0 1 2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialUnitPerpBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the actual unit perpendicular vector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The only denominator parameter is an upper bound for the reciprocal
squared length of the perpendicular product. -/
theorem weighted_unitPerp (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
    ∀ {s C K : ℝ} {X Y B : E → RVec 4}, 0 < s → 0 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ X U → ContDiffOn ℝ ∞ Y U → ContDiffOn ℝ ∞ B U →
      WeightedBound U s m C X → WeightedBound U s m C Y → WeightedBound U s m C B →
      (∀ x ∈ U, 0 < NormalFrame.perpProduct (X x) (Y x) (B x) ⬝ᵥ
        NormalFrame.perpProduct (X x) (Y x) (B x)) →
      (∀ x ∈ U, (NormalFrame.perpProduct (X x) (Y x) (B x) ⬝ᵥ
        NormalFrame.perpProduct (X x) (Y x) (B x))⁻¹ ≤ K) →
      WeightedBound U s m
        (2^m*((m.factorial : ℝ)*D*K^(m+1)*(1+dotBudget m (perpBudget m C))^m)*perpBudget m C)
        (fun x => NormalFrame.unitPerp (X x) (Y x) (B x)) := by
  obtain ⟨D,hD,hroot⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s C K X Y B hs hC hK hX hY hB bX bY bB hpos hi
  let P : E → RVec 4 := fun x => NormalFrame.perpProduct (X x) (Y x) (B x)
  have hP : ContDiffOn ℝ ∞ P U := contDiffOn_perpProduct hX hY hB
  have bP : WeightedBound U s m (perpBudget m C) P :=
    weighted_perpProduct hU hs hC hX hY hB bX bY bB
  have hPn := perpBudget_nonneg m hC
  have hS := contDiffOn_dot_real hP hP
  have bS : WeightedBound U s m (1+dotBudget m (perpBudget m C)) (fun x => P x ⬝ᵥ P x) :=
    (bP.dot_real_dup1 hU hs.le hPn hPn hP hP bP).mono_const (by
      change dotBudget m (perpBudget m C) ≤ 1+dotBudget m (perpBudget m C)
      linarith)
  have hS1 : 1 ≤ 1+dotBudget m (perpBudget m C) := by
    have hh := dotBudget_nonneg m hPn
    linarith
  have br := hroot hU hs hS1 hK hS hpos hi bS
  have hrootSmooth := (hS.sqrt (fun x hx => (hpos x hx).ne')).inv
    (fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne')
  exact br.smul_real_pi hU hs (by positivity) hPn hrootSmooth hP bP

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFreeNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the rational and square-root estimates to the actual free normal
of an immersed surface, with explicit inverse geometric margins. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma normalBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ normalBudget m C K := by
  have hh := liftBudget_nonneg m hC hK
  unfold normalBudget
  positivity

/-- The coefficient depends polynomially on the two-jet bound and the
inverse Gram and normal-length bounds. -/
theorem polynomial_freeNormal_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set Base} {F : RField 4}, ContDiff ℝ ∞ F →
      RealModeDomain F U → ∀ {s C K : ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      WeightedBound U s m C (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ K) →
      (∀ x ∈ U, (realSecond F x ⬝ᵥ realSecond F x)⁻¹ ≤ K) →
      WeightedBound U s m (freeNormalBudget m D C K) (freeNormal F) := by
  obtain ⟨D,hD,hunit⟩ := weighted_unitPerp (E := Base) m
  refine ⟨D,hD,?_⟩
  intro U F hF hU s C K hs hC hK hb hG hN
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hj : ContDiffOn ℝ ∞ (realTwoJet F) U := (contDiff_realTwoJet hF).contDiffOn
  have hX : ContDiffOn ℝ ∞ (coordDeriv dx F) U := (contDiff_real_coordDeriv hF dx).contDiffOn
  have hY : ContDiffOn ℝ ∞ (coordDeriv dy F) U := (contDiff_real_coordDeriv hF dy).contDiffOn
  have hW : ContDiffOn ℝ ∞ (coordDeriv dy (coordDeriv dy F)) U :=
    (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn
  have bX : WeightedBound U s m C (coordDeriv dx F) := hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 0
  have bY : WeightedBound U s m C (coordDeriv dy F) := hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 1
  have bW : WeightedBound U s m C (coordDeriv dy (coordDeriv dy F)) :=
    hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 4
  have bN : WeightedBound U s m (normalBudget m C K) (realSecond F) :=
    weighted_realNormalPart hU.isOpen.uniqueDiffOn hs hC hK hX hY hW bX bY bW hU.determinant hG
  have hNs := contDiffOn_realSecond hF hU
  let A := freeNormalInputBudget m C K
  have hnn := normalBudget_nonneg m hC0 hK0
  have hA : 0 ≤ A := by dsimp [A,freeNormalInputBudget] <;> linarith
  have hCA : C ≤ A := by dsimp [A,freeNormalInputBudget] <;> linarith
  have hNA : normalBudget m C K ≤ A := by dsimp [A,freeNormalInputBudget] <;> linarith
  have hK2 : 1 ≤ K^2 := by nlinarith
  apply hunit hU.isOpen.uniqueDiffOn hs hA hK2 hX hY hNs
    (bX.mono_const hCA) (bY.mono_const hCA) (bN.mono_const hNA)
  · intro x hx
    exact NormalFrame.perp_sq_pos (hU.determinant x hx) (hU.good x hx)
      (realNormalPart_perp _ _ _ (hU.determinant x hx)).1
      (realNormalPart_perp _ _ _ (hU.determinant x hx)).2
  · intro x hx
    have hn := realNormalPart_perp (coordDeriv dx F x) (coordDeriv dy F x)
      (coordDeriv dy (coordDeriv dy F) x) (hU.determinant x hx)
    change coordDeriv dx F x ⬝ᵥ realSecond F x = 0 ∧
      coordDeriv dy F x ⬝ᵥ realSecond F x = 0 at hn
    have hgpos := NormalFrame.gramDet_pos (hU.determinant x hx)
    have he : NormalFrame.perpProduct (coordDeriv dx F x) (coordDeriv dy F x) (realSecond F x) ⬝ᵥ
        NormalFrame.perpProduct (coordDeriv dx F x) (coordDeriv dy F x) (realSecond F x) =
        NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x)*
          (realSecond F x ⬝ᵥ realSecond F x) := by
      rw [NormalFrame.perp_sq,hn.1,hn.2]
      ring
    rw [he,mul_inv_rev]
    have hgb : (NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹ ≤ K :=
      (le_abs_self _).trans (hG x hx)
    simpa only [pow_two] using mul_le_mul (hN x hx) hgb
      (inv_nonneg.mpr hgpos.le) hK0

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialConnectionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the tangential reconstruction coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weighted_inverse_gramDet {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y : E → RVec 4} (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (inverseGramBudget m C K)
      (fun x => (NormalFrame.gramDet (X x) (Y x))⁻¹) := by
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have bG : WeightedBound U s m (quadraticBudget m C)
      (fun x => NormalFrame.gramDet (X x) (Y x)) := by
    convert weighted_quadratic_pair hU hs.le (zero_le_one.trans hC) hX hX hY hY bX bX bY bY using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    unfold NormalFrame.gramDet
    ring
  exact bG.inv_real hU hs (quadraticBudget_ge_one m (zero_le_one.trans hC)) hK hG hne hInv

theorem weighted_realConnections {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bW : WeightedBound U s m C W)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (liftBudget m C K) (fun x => realConnectionX (X x) (Y x) (W x)) ∧
    WeightedBound U s m (liftBudget m C K) (fun x => realConnectionY (X x) (Y x) (W x)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hq := zero_le_one.trans (quadraticBudget_ge_one m hC0)
  have hi := inverseGramBudget_nonneg m hC0 hK0
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have hGI := hG.inv hne
  have bInv := weighted_inverse_gramDet hU hs hC hK hX hY bX bY hne hInv
  have hnX := ((contDiffOn_dot_real hY hY).mul (contDiffOn_dot_real hX hW)).sub
    ((contDiffOn_dot_real hY hX).mul (contDiffOn_dot_real hY hW))
  have hnY := ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hW)).sub
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hX hW))
  have bnx := weighted_quadratic_pair hU hs.le hC0 hY hY hX hW bY bY bX bW
  have bny := weighted_quadratic_pair hU hs.le hC0 hX hX hY hW bX bX bY bW
  constructor
  · apply (bnx.mul_real_dup2 hU hs.le hq hi hnX hGI bInv).congr
    intro x hx
    change realConnectionX (X x) (Y x) (W x) = _
    simp only [realConnectionX,div_eq_mul_inv,dotProduct_comm]
    rfl
  · apply (bny.mul_real_dup2 hU hs.le hq hi hnY hGI bInv).congr
    intro x hx
    change realConnectionY (X x) (Y x) (W x) = _
    rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformRealModeCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reconstruction estimates on a fixed compact set of real two-jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

lemma admissibleComplexJets_domain : LowJet.Domain admissibleComplexJets := by
  refine ⟨?_,fun _ h => h.1,fun _ h => h.2⟩
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hs (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : TwoJet 4 => K i) J :=
    (ContinuousLinearMap.proj i : TwoJet 4 →L[ℝ] Ambient 4).contDiff.contDiffAt
  have hd := LowJet.contDiffAt_gramDet (hs 0) (hs 1)
  have hn := LowJet.contDiffAt_normalPart (hs 0) (hs 1) (hs 4) hJ.1
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((LowJet.contDiffAt_dot hn hn).continuousAt.eventually_ne hJ.2)

lemma complexifyJet_mem {J : RealTwoJet}
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0)
    (hB : realNormalPart (J 0) (J 1) (J 4) ≠ 0) :
    complexifyJetCLM J ∈ admissibleComplexJets := by
  constructor
  · change gramDet (complexify (J 0)) (complexify (J 1)) ≠ 0
    rw [complexify_gram]
    exact Complex.ofReal_ne_zero.mpr hD
  · change normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ⬝ᵥ
      normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ≠ 0
    rw [← complexify_normalPart,complexify_dot]
    exact Complex.ofReal_ne_zero.mpr ((dotProduct_self_eq_zero).not.mpr hB)

lemma twoJet_complexify {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    twoJet (fun p => complexify (F p)) = complexifyJetCLM ∘ realTwoJet F := by
  have hfirst (v : Base) : coordDeriv v (fun p => complexify (F p)) =
      fun p => complexify (coordDeriv v F p) := by
    funext p
    exact coordDeriv_complexify (hF.differentiable (by simp) p) v
  have hsecond (v w : Base) : coordDeriv v (fun p => complexify (coordDeriv w F p)) =
      fun p => complexify (coordDeriv v (coordDeriv w F) p) := by
    funext p
    exact coordDeriv_complexify ((contDiff_real_coordDeriv hF w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) v
  funext p i
  fin_cases i
  · change coordDeriv dx (fun p => complexify (F p)) p = complexify (coordDeriv dx F p)
    exact congrFun (hfirst dx) p
  · change coordDeriv dy (fun p => complexify (F p)) p = complexify (coordDeriv dy F p)
    exact congrFun (hfirst dy) p
  · change coordDeriv dx (coordDeriv dx (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dx F) p)
    rw [hfirst dx]
    exact congrFun (hsecond dx dx) p
  · change coordDeriv dx (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dx dy) p
  · change coordDeriv dy (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dy (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dy dy) p

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealJetCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real formulas for the reconstruction coefficients at an actual real
surface jet; complexification preserves every coefficient exactly. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma scalarCoefficients_complexify (J : RealTwoJet) (i : Fin 8) :
    LowJet.scalarCoefficients (complexifyJetCLM J) i = (realScalarCoefficients J i : ℂ) := by
  change LowJet.scalarCoefficients (fun k => complexify (J k)) i = _
  fin_cases i <;>
    simp [LowJet.scalarCoefficients,realScalarCoefficients,realConnectionX,
      realConnectionY,liftX,liftY,complexify_dot,complexify_gram,
      ← complexify_normalPart,realJetNormal]

lemma vectorCoefficients_complexify (J : RealTwoJet) (i : Fin 5) (a : Fin 4) :
    LowJet.vectorCoefficients (complexifyJetCLM J) i a = (realVectorCoefficients J i a : ℂ) := by
  change LowJet.vectorCoefficients (fun k => complexify (J k)) i a = _
  fin_cases i <;>
    simp [LowJet.vectorCoefficients,realVectorCoefficients,
      realTangentDualX,realTangentDualY,tangentLift,liftX,liftY,complexify_dot,complexify_gram,
      ← complexify_normalPart,realJetNormal]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDualBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial estimates for the three vector columns of reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weighted_realTangentDuals {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y : E → RVec 4} (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (tangentDualBudget m C K) (fun x => realTangentDualX (X x) (Y x)) ∧
    WeightedBound U s m (tangentDualBudget m C K) (fun x => realTangentDualY (X x) (Y x)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hdb := dotBudget_nonneg m hC0
  have hib := inverseGramBudget_nonneg m hC0 hK0
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have hGI := hG.inv hne
  have bi := weighted_inverse_gramDet hU hs hC hK hX hY bX bY hne hInv
  have bxx : WeightedBound U s m (dotBudget m C) (fun x => X x ⬝ᵥ X x) :=
    bX.dot_real_dup1 hU hs.le hC0 hC0 hX hX bX
  have bxy : WeightedBound U s m (dotBudget m C) (fun x => X x ⬝ᵥ Y x) :=
    bX.dot_real_dup1 hU hs.le hC0 hC0 hX hY bY
  have byy : WeightedBound U s m (dotBudget m C) (fun x => Y x ⬝ᵥ Y x) :=
    bY.dot_real_dup1 hU hs.le hC0 hC0 hY hY bY
  have hxx := (contDiffOn_dot_real hX hX).mul hGI
  have hxy := (contDiffOn_dot_real hX hY).mul hGI
  have hyy := (contDiffOn_dot_real hY hY).mul hGI
  have cxx := bxx.mul_real_dup2 hU hs.le hdb hib (contDiffOn_dot_real hX hX) hGI bi
  have cxy := bxy.mul_real_dup2 hU hs.le hdb hib (contDiffOn_dot_real hX hY) hGI bi
  have cyy := byy.mul_real_dup2 hU hs.le hdb hib (contDiffOn_dot_real hY hY) hGI bi
  have hc : 0 ≤ 2^m*dotBudget m C*inverseGramBudget m C K := by positivity
  have vxx := cxx.smul_real_pi hU hs hc hC0 hxx hY bY
  have vyx := cyy.smul_real_pi hU hs hc hC0 hyy hX bX
  have vxy := cxy.smul_real_pi hU hs hc hC0 hxy hX bX
  have vyy := cxy.smul_real_pi hU hs hc hC0 hxy hY bY
  constructor
  · have hh := vyx.sub hU hs.le (hyy.smul hX) (hxy.smul hY) vyy
    have hh' : WeightedBound U s m (tangentDualBudget m C K)
        (fun x => ((Y x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • X x-
          ((X x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x) := by
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      unfold tangentDualBudget
      ring
    apply hh'.congr
    intro x hx
    simp [realTangentDualX,div_eq_mul_inv,sub_eq_add_neg]
  · have hh := vxx.sub hU hs.le (hxx.smul hY) (hxy.smul hX) vxy
    have hh' : WeightedBound U s m (tangentDualBudget m C K)
        (fun x => ((X x ⬝ᵥ X x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x-
          ((X x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • X x) := by
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      unfold tangentDualBudget
      ring
    apply hh'.congr
    intro x hx
    simp [realTangentDualY,div_eq_mul_inv,sub_eq_add_neg,add_comm]

lemma weighted_vector_over_norm_sq {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C) (hK : 1 ≤ K)
    {V : E → RVec 4} (hV : ContDiffOn ℝ ∞ V U) (bV : WeightedBound U s m C V)
    (hpos : ∀ x ∈ U, 0 < V x ⬝ᵥ V x) (hi : ∀ x ∈ U, (V x ⬝ᵥ V x)⁻¹ ≤ K) :
    WeightedBound U s m (normalDualBudget m C K) (fun x => (V x ⬝ᵥ V x)⁻¹ • V x) := by
  have hdot := contDiffOn_dot_real hV hV
  have hd := dotBudget_nonneg m hC
  have bdot : WeightedBound U s m (1+dotBudget m C) (fun x => V x ⬝ᵥ V x) :=
    (bV.dot_real_dup1 hU hs.le hC hC hV hV bV).mono_const (by change dotBudget m C ≤ _; linarith)
  have hinv : ∀ x ∈ U, ‖(V x ⬝ᵥ V x)⁻¹‖ ≤ K := by
    intro x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hpos x hx).le)] using hi x hx
  have bi := bdot.inv_real hU hs (by linarith : 1 ≤ 1+dotBudget m C) hK hdot
    (fun x hx => (hpos x hx).ne') hinv
  exact bi.smul_real_pi hU hs (by positivity) hC (hdot.inv (fun x hx => (hpos x hx).ne')) hV bV

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRealReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common polynomial bound for every real reconstruction coefficient. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma reconstructionBudget_bounds (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    1 ≤ reconstructionBudget m C K ∧
    liftBudget m C K ≤ reconstructionBudget m C K ∧
    normalBudget m C K ≤ reconstructionBudget m C K ∧
    tangentDualBudget m C K ≤ reconstructionBudget m C K ∧
    normalDualBudget m (normalBudget m C K) K ≤ reconstructionBudget m C K ∧
    normalRatioBudget m (normalBudget m C K) K ≤ reconstructionBudget m C K := by
  have hl := liftBudget_nonneg m hC hK
  have hn : 0 ≤ normalBudget m C K := by unfold normalBudget; positivity
  have hi := inverseGramBudget_nonneg m hC hK
  have hd := dotBudget_nonneg m hC
  have hdn := dotBudget_nonneg m hn
  have ht : 0 ≤ tangentDualBudget m C K := by unfold tangentDualBudget; positivity
  have hnd : 0 ≤ normalDualBudget m (normalBudget m C K) K := by unfold normalDualBudget; positivity
  have hnr : 0 ≤ normalRatioBudget m (normalBudget m C K) K := by unfold normalRatioBudget; positivity
  unfold reconstructionBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The two inverse bounds concern the Gram determinant and the squared
length of the transverse second fundamental form. All derivatives are
estimated by explicit polynomials in these bounds and the two-jet bound. -/
theorem weighted_realJet_coefficients {U : Set E} (hU : UniqueDiffOn ℝ U)
    {J : E → RealTwoJet} (hJ : ContDiff ℝ ∞ J) {s C K : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K) (bJ : WeightedBound U s m C J)
    (hD : ∀ x ∈ U, NormalFrame.gramDet (J x 0) (J x 1) ≠ 0)
    (hN : ∀ x ∈ U, realJetNormal (J x) 4 ≠ 0)
    (hGD : ∀ x ∈ U, ‖(NormalFrame.gramDet (J x 0) (J x 1))⁻¹‖ ≤ K)
    (hGN : ∀ x ∈ U, ‖(realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)⁻¹‖ ≤ K) :
    (∀ i, WeightedBound U s m (reconstructionBudget m C K) (fun x => realScalarCoefficients (J x) i)) ∧
    (∀ i, WeightedBound U s m (reconstructionBudget m C K) (fun x => realVectorCoefficients (J x) i)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hJs (i : Fin 5) : ContDiff ℝ ∞ (fun x => J x i) := contDiff_pi.mp hJ i
  have bj (i : Fin 5) := bJ.component hU hs.le hC0 hJ.contDiffOn i
  have bc (i : Fin 5) := weighted_realConnections hU hs hC hK
    (hJs 0).contDiffOn (hJs 1).contDiffOn (hJs i).contDiffOn (bj 0) (bj 1) (bj i) hD hGD
  have bN (i : Fin 5) : WeightedBound U s m (normalBudget m C K) (fun x => realJetNormal (J x) i) :=
    weighted_realNormalPart hU hs hC hK (hJs 0).contDiffOn (hJs 1).contDiffOn
      (hJs i).contDiffOn (bj 0) (bj 1) (bj i) hD hGD
  have hNs (i : Fin 5) : ContDiffOn ℝ ∞ (fun x => realJetNormal (J x) i) U := by
    intro x hx
    exact (contDiffAt_realNormalPart (hJs 0).contDiffAt (hJs 1).contDiffAt
      (hJs i).contDiffAt (hD x hx)).contDiffWithinAt
  have hn0 : 0 ≤ normalBudget m C K := by
    have hh := liftBudget_nonneg m hC0 hK0
    unfold normalBudget
    positivity
  have hd0 := dotBudget_nonneg m hn0
  have hpos : ∀ x ∈ U, 0 < realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4 := by
    intro x hx
    have hh : 0 ≤ realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4 :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact hh.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr (hN x hx))
  have hplain : ∀ x ∈ U, (realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)⁻¹ ≤ K :=
    fun x hx => (le_abs_self _).trans (hGN x hx)
  have hsq := contDiffOn_dot_real (hNs 4) (hNs 4)
  have bsq : WeightedBound U s m (1+dotBudget m (normalBudget m C K))
      (fun x => realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4) :=
    ((bN 4).dot_real_dup1 hU hs.le hn0 hn0 (hNs 4) (hNs 4) (bN 4)).mono_const (by
      change dotBudget m (normalBudget m C K) ≤ _
      linarith)
  have binv := bsq.inv_real hU hs (by linarith : 1 ≤ 1+dotBudget m (normalBudget m C K))
    hK hsq (fun x hx => (hpos x hx).ne') hGN
  have hsqi := hsq.inv (fun x hx => (hpos x hx).ne')
  have hbi : 0 ≤ (m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m (normalBudget m C K))^m := by positivity
  have bratio (i : Fin 5) : WeightedBound U s m (normalRatioBudget m (normalBudget m C K) K)
      (fun x => (realJetNormal (J x) i ⬝ᵥ realJetNormal (J x) 4)/
        (realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)) := by
    have hh := ((bN i).dot_real_dup1 hU hs.le hn0 hn0 (hNs i) (hNs 4) (bN 4)).mul_real_dup2
      hU hs.le hd0 hbi (contDiffOn_dot_real (hNs i) (hNs 4)) hsqi binv
    exact hh.congr (fun x hx => div_eq_mul_inv _ _)
  have bduals := weighted_realTangentDuals hU hs hC hK (hJs 0).contDiffOn (hJs 1).contDiffOn
    (bj 0) (bj 1) hD hGD
  have bnormal := weighted_vector_over_norm_sq hU hs hn0 hK (hNs 4) (bN 4) hpos hplain
  obtain ⟨_,hbl,hbn,hbt,hbnd,hbnr⟩ := reconstructionBudget_bounds m hC0 hK0
  constructor
  · intro i
    fin_cases i
    · exact (bc 2).1.mono_const hbl
    · exact (bc 2).2.mono_const hbl
    · exact (bc 3).1.mono_const hbl
    · exact (bc 3).2.mono_const hbl
    · exact (bc 4).1.mono_const hbl
    · exact (bc 4).2.mono_const hbl
    · exact (bratio 2).mono_const hbnr
    · exact (bratio 3).mono_const hbnr
  · intro i
    fin_cases i
    · exact (bN 2).mono_const hbn
    · exact (bN 3).mono_const hbn
    · exact bduals.1.mono_const hbt
    · exact bduals.2.mono_const hbt
    · exact bnormal.mono_const hbnd

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

lemma freeNormalBudget_polynomial (m : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    HasPolynomialBound (fun x => freeNormalBudget m D x x) := by
  unfold freeNormalBudget freeNormalInputBudget perpBudget minorTermBudget crossBudget
    normalBudget liftBudget inverseGramBudget quadraticBudget dotBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

lemma reconstructionBudget_polynomial (m : ℕ) :
    HasPolynomialBound (fun x => reconstructionBudget m x x) := by
  unfold reconstructionBudget normalRatioBudget normalDualBudget tangentDualBudget
    normalBudget liftBudget inverseGramBudget quadraticBudget dotBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative reconstruction bounds for the actual complexified surface
map, derived from real two-jet and inverse denominator bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

theorem polynomial_reconstruction_bound {U : Set Base} {F : RField 4}
    (hF : ContDiff ℝ ∞ F) (hU : RealModeDomain F U) {s C K : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hb : WeightedBound U s m C (realTwoJet F))
    (hGD : ∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ K)
    (hGN : ∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ K) :
    ReconstructionCoefficientBound (fun p => complexify (F p)) U s m (reconstructionBudget m C K) := by
  let J := realTwoJet F
  have hJ : ContDiff ℝ ∞ J := contDiff_realTwoJet hF
  have hJn : ∀ x ∈ U, realJetNormal (J x) 4 ≠ 0 := hU.good
  obtain ⟨hscalar,hvector⟩ := weighted_realJet_coefficients hU.isOpen.uniqueDiffOn
    hJ hs hC hK hb hU.determinant hJn hGD hGN
  have hmap : MapsTo (complexifyJetCLM ∘ J) U admissibleComplexJets :=
    fun x hx => complexifyJet_mem (hU.determinant x hx) (hU.good x hx)
  have hcoeff := admissibleComplexJets_domain.smoothCoefficients.comp
    (complexifyJetCLM.contDiff.comp hJ).contDiffOn hmap
  have hsc (i : Fin 8) : ContDiffOn ℝ ∞ (fun x => realScalarCoefficients (J x) i) U := by
    have hh := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hcoeff (Sum.inl i))
    apply hh.congr
    intro x hx
    change realScalarCoefficients (J x) i = (LowJet.scalarCoefficients (complexifyJetCLM (J x)) i).re
    rw [scalarCoefficients_complexify,Complex.ofReal_re]
  have hvc (i : Fin 5) : ContDiffOn ℝ ∞ (fun x => realVectorCoefficients (J x) i) U := by
    apply contDiffOn_pi.mpr
    intro a
    have hh := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hcoeff (Sum.inr (i,a)))
    apply hh.congr
    intro x hx
    change realVectorCoefficients (J x) i a = (LowJet.vectorCoefficients (complexifyJetCLM (J x)) i a).re
    rw [vectorCoefficients_complexify,Complex.ofReal_re]
  have hcs (i : Fin 8) : WeightedBound U s m (reconstructionBudget m C K)
      (fun p => LowJet.scalarCoefficients (twoJet (fun p => complexify (F p)) p) i) := by
    have hh := weighted_linearIsometry hU.isOpen.uniqueDiffOn (hsc i) (hscalar i) Complex.ofRealLI
    apply hh.congr
    intro p hp
    change LowJet.scalarCoefficients (twoJet (fun p => complexify (F p)) p) i =
      (realScalarCoefficients (J p) i : ℂ)
    rw [show twoJet (fun p => complexify (F p)) p = complexifyJetCLM (J p) from
      congrFun (twoJet_complexify hF) p]
    exact scalarCoefficients_complexify (J p) i
  have hcv (i : Fin 5) : WeightedBound U s m (reconstructionBudget m C K)
      (fun p => LowJet.vectorCoefficients (twoJet (fun p => complexify (F p)) p) i) := by
    have hh := weighted_linearIsometry hU.isOpen.uniqueDiffOn (hvc i) (hvector i) (complexifyLI 4)
    apply hh.congr
    intro p hp
    change LowJet.vectorCoefficients (twoJet (fun p => complexify (F p)) p) i =
      complexify (realVectorCoefficients (J p) i)
    rw [show twoJet (fun p => complexify (F p)) p = complexifyJetCLM (J p) from
      congrFun (twoJet_complexify hF) p]
    ext a
    exact vectorCoefficients_complexify (J p) i a
  exact ⟨⟨⟨hcs 0,hcs 1,hcs 2,hcs 3,hcs 4,hcs 5,hcs 6,hcs 7⟩,hcv 0,hcv 1⟩,
    hcv 2,hcv 3,hcv 4⟩

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFrameEnvelope
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single polynomial envelope for the actual reconstruction coefficients
and free normal. Its degree is chosen before any geometric bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4
open WeightedEstimates

namespace SmallModes

lemma ReconstructionCoefficientBound.mono_const {n : ℕ} {F : Field n}
    {U : Set Base} {s C D : ℝ} {m : ℕ}
    (h : ReconstructionCoefficientBound F U s m C) (hCD : C ≤ D) :
    ReconstructionCoefficientBound F U s m D :=
  ⟨⟨⟨h.xxX.mono_const hCD,h.xxY.mono_const hCD,h.xyX.mono_const hCD,
      h.xyY.mono_const hCD,h.yyX.mono_const hCD,h.yyY.mono_const hCD,
      h.ratioxx.mono_const hCD,h.ratioxy.mono_const hCD⟩,
      h.secondxx.mono_const hCD,h.secondxy.mono_const hCD⟩,
      h.dualx.mono_const hCD,h.dualy.mono_const hCD,h.dualn.mono_const hCD⟩

end SmallModes

namespace RealModes
open SmallModes

theorem polynomial_frame_envelope (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ {U : Set Base} {F : RField 4}, ContDiff ℝ ∞ F → RealModeDomain F U →
      ∀ {s B : ℝ}, 0 < s → 1 ≤ B →
      WeightedBound U s m B (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ B) →
      ReconstructionCoefficientBound (fun x => complexify (F x)) U s m (A*B^d) ∧
      WeightedBound U s m (A*B^d) (freeNormal F) := by
  obtain ⟨D,hD,hfree⟩ := polynomial_freeNormal_bound m
  obtain ⟨d,A,hA,hpoly⟩ :=
    (reconstructionBudget_polynomial m).add (freeNormalBudget_polynomial m (zero_le_one.trans hD))
  refine ⟨d,A,hA,?_⟩
  intro U F hF hU s B hs hB hb hG hN
  have hp := hpoly B hB
  have hfb : 0 ≤ freeNormalBudget m D B B := by
    unfold freeNormalBudget freeNormalInputBudget
    have hnormal := normalBudget_nonneg m (zero_le_one.trans hB) (zero_le_one.trans hB)
    unfold perpBudget minorTermBudget crossBudget dotBudget
    positivity
  have hrb := (reconstructionBudget_bounds m (zero_le_one.trans hB) (zero_le_one.trans hB)).1
  constructor
  · exact (polynomial_reconstruction_bound hF hU hs hB hB hb hG hN).mono_const
      ((le_add_of_nonneg_right hfb).trans hp.2)
  · exact (hfree hF hU hs hB hB hb hG
      (fun x hx => (le_abs_self _).trans (hN x hx))).mono_const
      ((le_add_of_nonneg_left (zero_le_one.trans hrb)).trans hp.2)

end RealModes
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalDenominatorMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert geometric lower margins into the reciprocal bounds used by the
quantitative reconstruction and normal-frame estimates. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma norm_le_sqrt_dot_self (V : RVec 4) : ‖V‖ ≤ Real.sqrt (V ⬝ᵥ V) := by
  have hd : 0 ≤ V ⬝ᵥ V := Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hd,Real.norm_eq_abs,sq_abs]
  simpa only [pow_two,dotProduct] using
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (V j)) (Finset.mem_univ i))

lemma norm_inv_dot_self_le {V : RVec 4} {b : ℝ} (hb : 0 < b) (hV : b ≤ ‖V‖) :
    ‖(V ⬝ᵥ V)⁻¹‖ ≤ (b^2)⁻¹ := by
  have hd : 0 ≤ V ⬝ᵥ V := Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)
  have hs : b ≤ Real.sqrt (V ⬝ᵥ V) := hV.trans (norm_le_sqrt_dot_self V)
  have hsq : b^2 ≤ V ⬝ᵥ V := by
    nlinarith [Real.sq_sqrt hd]
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hd)]
  exact (inv_le_inv₀ ((sq_pos_of_pos hb).trans_le hsq) (sq_pos_of_pos hb)).mpr hsq

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearPhaseFrameMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Gram and transverse-normal denominators in nonlinear
first-coordinate phase charts. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_det_inv (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (coordDet (fderiv ℝ e.symm y))⁻¹ = coordDet (fderiv ℝ e (e.symm y)) := by
  have hd := congrArg coordDet (inverse_chart_derivative e he hi hy)
  rw [coordDet_comp,coordDet_id] at hd
  have hn : coordDet (fderiv ℝ e.symm y) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hd
    exact zero_ne_one hd
  have hh := congrArg (fun t => t*(coordDet (fderiv ℝ e.symm y))⁻¹) hd
  simpa only [mul_assoc,mul_inv_cancel₀ hn,mul_one,one_mul] using hh.symm

lemma realSecond_nonlinear_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) (hphase : ∀ x, (e x).1 = φ x)
    {y : Base} (hy : y ∈ e.target)
    (hImm : Function.Injective (fderiv ℝ F (e.symm y))) :
    realSecond (F ∘ e.symm) y = (coordDet (fderiv ℝ e.symm y))^2 •
      secondQuadratic (realSecondTensor F (e.symm y))
        (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1) := by
  have hdet := coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source
    hi.contDiffOn he.contDiffOn (fun z hz => e.map_target hz) (fun z hz => e.right_inv hz) hy
  have hh := phase_length_comp_smooth hF hi (phaseDerivative φ (e.symm y)) y
    (gramDet_ne_zero_of_injective _ hImm) hdet
  rw [inverse_chart_phase_covector hφ e hi hphase hy] at hh
  have hdx : (-(dx : Base).2,(dx : Base).1) = dy := by simp [dx,dy]
  rw [hdx] at hh
  change secondQuadratic (realSecondTensor (F ∘ e.symm) y) dy = _ at hh
  change realSecondForm (F ∘ e.symm) dy dy y = _
  rw [realSecondForm_quadratic (hF.comp hi)]
  exact hh

theorem inverse_gram_nonlinear_chart_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target)
    {D K : ℝ} (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdet : |coordDet (fderiv ℝ e (e.symm y))| ≤ D)
    (hG : ‖(NormalFrame.gramDet (coordDeriv dx F (e.symm y))
      (coordDeriv dy F (e.symm y)))⁻¹‖ ≤ K) :
    ‖(NormalFrame.gramDet (coordDeriv dx (F ∘ e.symm) y)
      (coordDeriv dy (F ∘ e.symm) y))⁻¹‖ ≤ K*D^2 := by
  have hg := gramDet_comp_smooth hF hi y
  change _ = (coordDet (fderiv ℝ e.symm y))^2 * _ at hg
  rw [hg,mul_inv_rev,← inv_pow,norm_mul,norm_pow,inverse_chart_det_inv e he hi hy,
    Real.norm_eq_abs]
  exact mul_le_mul hG (pow_le_pow_left₀ (abs_nonneg _) hdet 2) (by positivity) hK

theorem inverse_normal_nonlinear_chart_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) (hphase : ∀ x, (e x).1 = φ x)
    {y : Base} (hy : y ∈ e.target) {D K : ℝ} (_hD : 0 ≤ D)
    (hdet : |coordDet (fderiv ℝ e (e.symm y))| ≤ D)
    (hImm : Function.Injective (fderiv ℝ F (e.symm y)))
    (hgood : Good (realSecondTensor F (e.symm y)) (phaseDerivative φ (e.symm y)))
    (hN : ‖secondQuadratic (realSecondTensor F (e.symm y))
      (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1)‖⁻¹ ≤ K) :
    ‖(realSecond (F ∘ e.symm) y ⬝ᵥ realSecond (F ∘ e.symm) y)⁻¹‖ ≤ K^2*D^4 := by
  let S := secondQuadratic (realSecondTensor F (e.symm y))
    (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1)
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hgood.2
  have hSi : ‖(S ⬝ᵥ S)⁻¹‖ ≤ K^2 := by
    have hh := norm_inv_dot_self_le hSn le_rfl
    rw [← inv_pow] at hh
    exact hh.trans (pow_le_pow_left₀ (inv_nonneg.mpr hSn.le) hN 2)
  rw [realSecond_nonlinear_chart hF hφ e he hi hphase hy hImm,
    smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul,mul_inv_rev,← inv_pow,norm_mul,norm_pow,
    inverse_chart_det_inv e he hi hy]
  calc
    _ ≤ K^2*D^2*D^2 := by
      gcongr
      · simpa only [Real.norm_eq_abs] using hdet
      · simpa only [Real.norm_eq_abs] using hdet
    _ = K^2*D^4 := by ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNonlinearPhaseFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial reconstruction bounds for nonlinear first-coordinate phase
charts, including the cross-chart quadratic phases. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

theorem polynomial_nonlinear_phase_frame_bound (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ (F : RField 4) (φ : Base → ℝ) (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
      (∀ x, (e x).1 = φ x) →
    ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
      (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
      (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B) →
      (∀ x ∈ e.source, Function.Injective (fderiv ℝ F x)) →
      (∀ x ∈ e.source, Good (realSecondTensor F x) (phaseDerivative φ x)) →
      (∀ x ∈ e.source,
        ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor F x)
        (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) →
      ReconstructionCoefficientBound (fun x => complexify ((F ∘ e.symm) x))
        e.target s m (A*B^d) ∧
      WeightedBound e.target s m (A*B^d) (freeNormal (F ∘ e.symm)) := by
  obtain ⟨d₀,A₀,hA₀,hjet⟩ := polynomial_inverse_chart_twoJet_bound m
  obtain ⟨q,C,hC,hframe⟩ := polynomial_frame_envelope m
  let S : ℝ → ℝ := fun B => 1+A₀*B^d₀+B^3+B^6
  have hp : HasPolynomialBound S := by
    dsimp [S]
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,A,hA,hpoly⟩ := (polynomialBound_const (zero_le_one.trans hC)).mul (hp.pow q)
  refine ⟨d,A,hA,?_⟩
  intro F φ e hF hφ he hi hphase s B hs hs1 hB hFj hej heinv hedet hImm hgood hG hN
  have hB0 := zero_le_one.trans hB
  have hterms : 1 ≤ S B ∧ A₀*B^d₀ ≤ S B ∧ B^3 ≤ S B ∧ B^6 ≤ S B := by
    have h0 : 0 ≤ A₀*B^d₀ := mul_nonneg (zero_le_one.trans hA₀) (pow_nonneg hB0 _)
    have h3 : 0 ≤ B^3 := pow_nonneg hB0 _
    have h6 : 0 ≤ B^6 := pow_nonneg hB0 _
    dsimp [S]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hj := (hjet F e hF he hi s B hs hs1 hB hFj hej heinv).mono_const hterms.2.1
  have hdomain := realModeDomain_smooth_phase_chart hF hφ e he hi hphase hImm hgood
  obtain ⟨hc,hf⟩ := hframe (hF.comp hi) hdomain hs hterms.1 hj
    (fun y hy => (inverse_gram_nonlinear_chart_bound hF e he hi hy hB0 hB0
      (hedet _ (e.map_target hy)) (hG _ (e.map_target hy))).trans (by
        convert hterms.2.2.1 using 1
        all_goals try with_reducible_and_instances rfl
        ring))
    (fun y hy => (inverse_normal_nonlinear_chart_bound hF hφ e he hi hphase hy hB0
      (hedet _ (e.map_target hy)) (hImm _ (e.map_target hy))
      (hgood _ (e.map_target hy)) (hN _ (e.map_target hy))).trans (by
        convert hterms.2.2.2 using 1
        all_goals try with_reducible_and_instances rfl
        ring))
  exact ⟨hc.mono_const (hpoly B hB).2,hf.mono_const (hpoly B hB).2⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNonlinearSolver
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite metric-mode solvers in nonlinear phase charts, with all
coefficient and coordinate budgets specified polynomially. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_nonlinear_unperturbed_solver_oai :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
      (_he : ContDiff ℝ ∞ e) (_hi : ContDiff ℝ ∞ e.symm),
      (∀ x, (e x).1 = coordinatePhase φ x) →
      (modeSupport K : Set SmallModes.Base) ⊆ e.source →
      (∀ x ∈ e.source, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ e.source, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m,
        (∀ j ≤ m+3, WeightedBound e.source 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ j, 1 ≤ j → j ≤ m+3 → ∀ x ∈ e.source,
          ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B m) ∧
        (∀ x ∈ e.source, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ B m)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e ∧ (∀ m, c.C m = A m*(B m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = B m) := by
  classical
  choose p A hA hframe using fun m => polynomial_nonlinear_phase_frame_bound (m+1)
  refine ⟨p,A,hA,?_⟩
  intro G hG K φ hφ e he hi hphase hKe hImm hgood τ s hs hs1 B hB hb
  have hF : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hφ' : ContDiff ℝ ∞ (coordinatePhase φ) := hφ.comp planeCoordinateIsometry.symm.contDiff
  have hdom := realModeDomain_smooth_phase_chart hF hφ' e he hi hphase hImm hgood
  have hc (m : ℕ) : SmallModes.ReconstructionCoefficientBound
      (fun x => complexify (G (planeCoordinateIsometry.symm (e.symm x))))
      e.target s (m+1) (A m*(B m)^(p m)) := by
    obtain ⟨hFj,hej,hei,hed,hgram,hnormal⟩ := hb m
    have hh := (hframe m _ _ e hF hφ' he hi hphase s (B m) hs hs1 (hB m)
      (fun j hj => hFj j (by omega))
      (fun j hj hjm x hx => hej j hj (by omega) x hx)
      hei hed hImm hgood hgram hnormal).1
    exact hh
  have hC (m : ℕ) : 0 ≤ A m*(B m)^(p m) :=
    mul_nonneg (zero_le_one.trans (hA m)) (pow_nonneg (zero_le_one.trans (hB m)) _)
  let c := unperturbedSolverOfBounds hG K hφ e he hi hKe (fun x _ => hphase x)
    hdom τ s (fun m => A m*(B m)^(p m)) B hC hB hc
      (fun m j hj hjm x hx => (hb m).2.1 j hj (by omega) x hx)
  exact ⟨c,rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver_oai
