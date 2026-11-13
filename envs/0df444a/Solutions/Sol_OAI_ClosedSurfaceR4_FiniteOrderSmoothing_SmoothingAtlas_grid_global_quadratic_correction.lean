-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:25.050653+00:00
-- url     : https://prove2.me/submissions/31105103-9e64-4299-b7ff-75958713228a

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_catalog_atlas_cancellation

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

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

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

lemma WeightedBound.dot {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : E → ι → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ) * (2 ^ m * C * D))
      (fun x => dotProduct (f x) (g x)) := by
  have hfsm (i : ι) := contDiffOn_pi.mp hf i
  have hgsm (i : ι) := contDiffOn_pi.mp hg i
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2 ^ m * C * D)
    (fun i x => f x i * g x i) (fun i _ => (hfsm i).mul (hgsm i)) (fun i _ =>
      (hbf.component hU hs hC hf i).mul hU hs hC hD (hfsm i) (hgsm i)
        (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct] using hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
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

section Quantitative
variable {n : ℕ}



lemma weighted_smul_field {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f : Scalar} {V : Field n} (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hbf : WeightedBound U s m C f) (hbV : WeightedBound U s m D V) :
    WeightedBound U s m (2 ^ m * C * D) (fun p => f p • V p) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hV i)
  · intro i
    exact hbf.mul hU hs.le hC hD hf (contDiffOn_pi.mp hV i) (hbV.component hU hs.le hD hV i)



end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticError
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
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_conjugate {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Base → CVec n} (hs : 0 < s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hbZ : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => conjugate (Z p)) := by
  apply WeightedBound.pi hU hs hC
  · intro i
    exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)
  · intro i
    have hh := (hbZ.component hU hs.le hC hZ i).linear hU hs.le
      (contDiffOn_pi.mp hZ i) Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp



end ClosedSurfaceR4.QuadraticMean

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

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma norm_phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ =
      (coordDet (fderiv ℝ φ p))^2 *
        ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by
  rw [phase_length_comp_smooth hF hφ ξ p hD hdet,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_realSecondForm_le {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    ‖realSecondForm F v w p‖ ≤ 4*‖realSecondTensor F p‖*‖v‖*‖w‖ := by
  have h11 : |v.1*w.1| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_fst_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h22 : |v.2*w.2| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_snd_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h12 : |v.1*w.2+v.2*w.1| ≤ 2*‖v‖*‖w‖ := by
    have ha : |v.1*w.2| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_snd_le w)
        (abs_nonneg _) (norm_nonneg _)
    have hb : |v.2*w.1| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_fst_le w)
        (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (v.1*w.2) (v.2*w.1)]
  rw [realSecondForm_bilinear hF]
  calc
    _ ≤ (‖(v.1*w.1) • realSecondTensor F p 0‖+
        ‖(v.1*w.2+v.2*w.1) • realSecondTensor F p 1‖)+
        ‖(v.2*w.2) • realSecondTensor F p 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖*‖w‖*‖realSecondTensor F p‖+
        (2*‖v‖*‖w‖)*‖realSecondTensor F p‖)+‖v‖*‖w‖*‖realSecondTensor F p‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm _ 0
      · exact norm_le_pi_norm _ 1
      · exact norm_le_pi_norm _ 2
    _ = _ := by ring

lemma norm_realSecondTensor_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤
      4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  have hbound (v : Base) (hv : ‖v‖ = 1) : ‖fderiv ℝ φ p v‖ ≤ ‖fderiv ℝ φ p‖ := by
    simpa only [hv,mul_one] using (fderiv ℝ φ p).le_opNorm v
  have hx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have hb (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖realSecondForm (F ∘ φ) v w p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
    rw [realSecondForm_comp_smooth hF hφ _ _ _ hD hdet]
    calc
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p v‖*‖fderiv ℝ φ p w‖ :=
        norm_realSecondForm_le hF _ _ _
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖*‖fderiv ℝ φ p‖ := by
        gcongr
        · exact hbound v hv
        · exact hbound w hw
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact hb dx dx hx hx
  · exact hb dx dy hx hy
  · exact hb dy dy hy hy

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

lemma continuous_coordDet : Continuous coordDet := by
  unfold coordDet
  fun_prop

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



theorem compact_chart_jacobian_bounds {φ ψ : Base → Base} {U V K : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ p ∈ K, d ≤ |coordDet (fderiv ℝ φ p)| ∧ ‖fderiv ℝ φ p‖ ≤ C := by
  have hD : ContinuousOn (fderiv ℝ φ) K :=
    (hφ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hd : ContinuousOn (fun p => |coordDet (fderiv ℝ φ p)|) K :=
    (continuous_coordDet.comp_continuousOn hD).abs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hD
  by_cases hn : K.Nonempty
  · obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hn hd
    refine ⟨|coordDet (fderiv ℝ φ p)|,|C|+1,abs_pos.mpr ?_,by positivity,?_⟩
    · exact coordDet_fderiv_ne_zero_of_local_inverse hU hV hφ hψ hmap hinv (hKU hp)
    · intro q hq
      exact ⟨hm hq,(hC q hq).trans (by linarith [le_abs_self C])⟩
  · exact ⟨1,1,zero_lt_one,zero_lt_one,fun p hp => False.elim (hn ⟨p,hp⟩)⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma coordDeriv_eventuallyEq {n : ℕ} {F G : RField n} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v : Base) : coordDeriv v F =ᶠ[𝓝 p] coordDeriv v G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v) hq

lemma realSecondForm_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    (fun q => realSecondForm F v w q) =ᶠ[𝓝 p] (fun q => realSecondForm G v w q) := by
  filter_upwards [coordDeriv_eventuallyEq h dx, coordDeriv_eventuallyEq h dy,
    coordDeriv_eventuallyEq (coordDeriv_eventuallyEq h w) v] with q hx hy hxy
  simp only [realSecondForm, hx, hy, hxy]

lemma realSecondTensor_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) : realSecondTensor F =ᶠ[𝓝 p] realSecondTensor G := by
  filter_upwards [realSecondForm_eventuallyEq h dx dx, realSecondForm_eventuallyEq h dx dy,
    realSecondForm_eventuallyEq h dy dy] with q hxx hxy hyy
  ext i
  fin_cases i <;> simp [realSecondTensor, hxx, hxy, hyy]




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



theorem coordinateTransition_compact_bounds (q p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ (coordinateTransition q p).source) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ x ∈ K, d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)| ∧
        ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ C := by
  let e := coordinateTransition q p
  exact compact_chart_jacobian_bounds e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun x hx => e.left_inv hx) hK hKs

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LengthMargins
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

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma norm_secondQuadratic_rotated_smul {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) (a : ℝ) :
    ‖secondQuadratic B (-(a • ξ).2,(a • ξ).1)‖ =
      a^2*‖secondQuadratic B (-ξ.2,ξ.1)‖ := by
  have he : (-(a • ξ).2,(a • ξ).1) = a • (-ξ.2,ξ.1) := by
    ext <;> simp [mul_neg]
  rw [he,secondQuadratic_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg a)]

lemma good_of_direction_length_pos {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    (h : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖) : Good B ξ := by
  refine ⟨?_, norm_pos_iff.mp h⟩
  intro hξ
  simp [hξ,secondQuadratic] at h





end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma norm_pullCovector_le (A : Base →L[ℝ] Base) (ξ : Base) :
    ‖pullCovector A ξ‖ ≤ 2*‖A‖*‖ξ‖ := by
  have hd : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have he : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have bound (v : Base) (hv : ‖v‖ = 1) : |ξ.1*(A v).1+ξ.2*(A v).2| ≤ 2*‖A‖*‖ξ‖ := by
    have hA : ‖A v‖ ≤ ‖A‖ := by simpa only [hv,mul_one] using A.le_opNorm v
    have h1 : |ξ.1*(A v).1| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le ξ)
        ((show |(A v).1| ≤ ‖A v‖ by simpa using norm_fst_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    have h2 : |ξ.2*(A v).2| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le ξ)
        ((show |(A v).2| ≤ ‖A v‖ by simpa using norm_snd_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (ξ.1*(A v).1) (ξ.2*(A v).2)]
  change max ‖ξ.1*(A dx).1+ξ.2*(A dx).2‖ ‖ξ.1*(A dy).1+ξ.2*(A dy).2‖ ≤ _
  simpa only [Real.norm_eq_abs,max_le_iff] using And.intro (bound dx hd) (bound dy he)




theorem quantitative_chart_phase_margin {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  have hdet0 : coordDet (fderiv ℝ φ p) ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  have hsq : d^2 ≤ (coordDet (fderiv ℝ φ p))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hd.le hdet 2
  have hbc : ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*C ^ 2 := by
    apply (norm_realSecondTensor_comp_smooth hF hφ p hD hdet0).trans
    gcongr
  have hlength := norm_phase_length_comp_smooth hF hφ ξ p hD hdet0
  have hbound : d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    calc
      _ ≤ d^2*ε/(4*C ^ 2)*(4*‖realSecondTensor F (φ p)‖*C ^ 2) := by gcongr
      _ = d^2*(ε*‖realSecondTensor F (φ p)‖) := by field_simp
      _ ≤ d^2*‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hpos : 0 < ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    exact mul_pos (sq_pos_of_ne_zero hdet0) ((mul_pos hε (norm_pos_iff.mpr hB)).trans_le hmargin)
  refine ⟨(norm_pullCovector_le _ _).trans ?_,hbound,good_of_direction_length_pos _ _ hpos,?_⟩
  · gcongr
  · intro hz
    simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,norm_zero] at hpos
    exact lt_irrefl 0 hpos

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter




theorem quantitative_chart_phase_margin_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (ξ : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hTG := (realSecondTensor_eventuallyEq heG).eq_of_nhds
  have hTF := (realSecondTensor_eventuallyEq hecomp).eq_of_nhds
  have h := quantitative_chart_phase_margin hG.contDiff hΦ.contDiff ξ p hd hC hε hDG
    (by simpa only [eD] using hdet) (by simpa only [eD] using hA)
    (by simpa only [ep,hTG] using hB) (by simpa only [ep,hTG] using hmargin)
  simpa only [eD,hTF] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q (coordinateTransition q p x) = coordinateMap F p x := by
  change spaceCoordinates (F (coordinateInverse q (coordinateTransition q p x))) =
    spaceCoordinates (F (coordinateInverse p x))
  rw [← coordinateChart_symm_apply, ← coordinateChart_symm_apply]
  change spaceCoordinates (F ((coordinateChart q).symm
    (coordinateChart q ((coordinateChart p).symm x)))) = _
  have hqx : (coordinateChart p).symm x ∈ (coordinateChart q).source := hx.2
  rw [(coordinateChart q).left_inv hqx]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition_eventuallyEq (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q ∘ coordinateTransition q p =ᶠ[𝓝 x] coordinateMap F p := by
  filter_upwards [(coordinateTransition q p).open_source.mem_nhds hx] with y hy
  exact coordinateMap_transition F q p hy




theorem actual_chart_phase_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) (ξ : SmallModes.Base)
    {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
      (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) x‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
        (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
          (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) x)
      (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
    realSecondTensor (coordinateMap F p) x ≠ 0 := by
  have hy : coordinateTransition q p x ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hx.2
  have ht := quantitative_chart_phase_margin_on
    (coordinateTransition q p).open_source (coordinateDomain_open q)
    (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx hy ξ hd hL hε hD hdet hA hB hmargin
  have he := (realSecondTensor_eventuallyEq
    (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds
  simpa only [he] using ht

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_compact_image {K : Set M} (hK : IsCompact K) (p : M)
    (hKs : K ⊆ (coordinateChart p).source) :
    IsCompact (coordinateChart p '' K) := hK.image_of_continuousOn ((coordinateChart p).continuousOn.mono hKs)

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_image_overlap {K : Set M} (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    coordinateChart p '' K ⊆ (coordinateTransition q p).source := by
  rintro x ⟨a,ha,rfl⟩
  constructor
  · exact (coordinateChart p).map_source (hKp ha)
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rw [(coordinateChart p).left_inv (hKp ha)]
    exact hKq ha




end ClosedSurfaceR4

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasLabels
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
  [IsManifold planeModel ∞ M] {ι : Type*} [Fintype ι]



theorem finite_atlas_transition_bounds (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i)) :
    ∃ d L : ℝ, 0 < d ∧ 0 < L ∧ ∀ i j : ι,
      ∀ x ∈ coordinateChart (p i) '' (tsupport (ψ i) ∩ tsupport (ψ j)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p j) (p i)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p j) (p i)) x‖ ≤ L := by
  classical
  have hs (i : ι) : tsupport (ψ i) ⊆ (coordinateChart (p i)).source := by
    rw [coordinateChart_source]
    exact hsource i
  have hb (a : ι × ι) : ∃ d L : ℝ, 0 < d ∧ 0 < L ∧
      ∀ x ∈ coordinateChart (p a.1) '' (tsupport (ψ a.1) ∩ tsupport (ψ a.2)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x‖ ≤ L := by
    have hK := (hcompact a.1).inter_right (isClosed_tsupport (ψ a.2))
    exact coordinateTransition_compact_bounds (p a.2) (p a.1)
      (coordinateChart_compact_image hK (p a.1) (fun x hx => hs a.1 hx.1))
      (coordinateChart_image_overlap (p a.2) (p a.1)
        (fun x hx => hs a.1 hx.1) (fun x hx => hs a.2 hx.2))
  choose d L hd hL hbound using hb
  obtain ⟨d₀,hd₀,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨d₀,1+∑ a, L a,hd₀,?_,?_⟩
  · have hn : 0 ≤ ∑ a, L a := Finset.sum_nonneg (fun a _ => le_of_lt (hL a))
    linarith
  · intro i j x hx
    refine ⟨(hle (i,j)).trans ((hbound (i,j) x hx).1),?_⟩
    have hsL : L (i,j) ≤ ∑ a, L a :=
      Finset.single_le_sum (fun a _ => le_of_lt (hL a)) (Finset.mem_univ (i,j))
    exact ((hbound (i,j) x hx).2).trans (by linarith)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma phaseDerivative_linear_comp {φ : SmallModes.Base → SmallModes.Base}
    {x : SmallModes.Base} (hφ : DifferentiableAt ℝ φ x) (ξ : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ ∘ φ) x = pullCovector (fderiv ℝ φ x) ξ := by
  have hd := ((phaseLinear ξ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
  unfold phaseDerivative
  rw [hd]
  rfl



theorem actual_phase_differential (q p : M) (ξ : SmallModes.Base)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ := by
  change phaseDerivative (phaseLinear ξ ∘ coordinateTransition q p) x = _
  have hc := ((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact phaseDerivative_linear_comp (hc.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ξ

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



theorem actual_phase_margin_at {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source)
    (ξ : SmallModes.Base) {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) (coordinateChart p a))|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) (coordinateChart p a)‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateChart q a) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateChart q a)) (-ξ.2,ξ.1)‖) :
    ‖atlasPhaseCovector q p ξ a‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) (coordinateChart p a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) (coordinateChart p a))
        (-(atlasPhaseCovector q p ξ a).2,(atlasPhaseCovector q p ξ a).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) (coordinateChart p a))
      (atlasPhaseCovector q p ξ a) ∧
    realSecondTensor (coordinateMap F p) (coordinateChart p a) ≠ 0 := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have he := coordinateTransition_apply_chart q p hap
  have h := actual_chart_phase_margin hF q p hx ξ hd hL hε
    (by simpa only [he] using hD) hdet hA
    (by simpa only [he] using hB) (by simpa only [he] using hmargin)
  unfold atlasPhaseCovector
  rw [actual_phase_differential q p ξ hx]
  exact h

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
attribute [-instance] _root_.instVAddIntReal_solutions
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma norm_firstDirection (i : Fin 3) : ‖firstDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [firstDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | norm_num [firstDirection, dx, dy, Prod.norm_def])

lemma norm_secondDirection (i : Fin 3) : ‖secondDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [secondDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | norm_num [secondDirection, dx, dy, Prod.norm_def])

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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




lemma weighted_derivativeAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → CVec n} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (derivativeAmplitude τ φ Z v) := by
  have hd := (hb.directional hU hs hZ v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hdφ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hφ v
  have hc := weighted_real_complex hU.uniqueDiffOn hs.le hP hdφ hp
  have hcs := Complex.ofRealCLM.contDiff.comp_contDiffOn hdφ
  have hc' := hc.const_mul hU.uniqueDiffOn hcs (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ)) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) U := by
    exact contDiffOn_const.mul hcs
  have hz := ClosedSurfaceR4.SmallModes.weighted_smul_field hU.uniqueDiffOn hs
    (show 0 ≤ 1 / τ * P by positivity) hC hcm hZ hc'
    (hb.mono_order (Nat.le_succ m))
  have hzs : ContDiffOn ℝ ∞
      (fun p => (Complex.I / (τ : ℂ) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) • Z p) U := by
    exact hcm.smul hZ
  have ha := hd'.add hU.uniqueDiffOn hs.le
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hZ v) hzs hz
  convert ha using 1 <;> first | rfl | ring

lemma weighted_halfDot {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {X Y : Base → CVec n} {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : WeightedBound U s m C X) (hbY : WeightedBound U s m D Y) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * C * D)) (fun p => (X p ⬝ᵥ Y p) / 2) := by
  have hh := (hbX.dot hU hs hC hD hX hY hbY).const_mul hU (contDiffOn_dot hX hY) (1 / 2 : ℂ)
  apply (hh.congr (fun p _ => by ring)).mono_const
  simp only [norm_div, norm_one, Complex.norm_ofNat, Fintype.card_fin]
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * C * D) := by positivity
  nlinarith

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)



theorem weighted_phaseCrossTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} {τ s C D P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (hbZ : WeightedBound U s (m + 1) C Z) (hbW : WeightedBound U s (m + 1) D W)
    (hpφ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ))
    (hpψ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v ψ)) :
    let A := (1 + 2 ^ m * P) * C / τ
    let B := (1 + 2 ^ m * P) * D / τ
    WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phasePlusTensor τ φ ψ Z W) ∧
      WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phaseMinusTensor τ φ ψ Z W) := by
  dsimp only
  have hA : 0 ≤ (1 + 2 ^ m * P) * C / τ := by positivity
  have hB : 0 ≤ (1 + 2 ^ m * P) * D / τ := by positivity
  have hdZ (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hC hP hφ hZ hbZ v hv (hpφ v hv)
  have hdW (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hD hP hψ hW hbW v hv (hpψ v hv)
  have hsZ (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ v
  have hsW (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ v
  constructor
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phasePlusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _) (hsW _)
        (hdZ _ (norm_firstDirection i)) (hdW _ (norm_secondDirection i))
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phaseMinusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _)
        (QuadraticMean.contDiffOn_conjugate (hsW _)) (hdZ _ (norm_firstDirection i))
        (QuadraticMean.weighted_conjugate hU.uniqueDiffOn hs hB (hsW _)
          (hdW _ (norm_secondDirection i)))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseDifferentials
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma phaseDerivative_add {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f+g) x = phaseDerivative f x + phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_add hf hg]
  rfl

lemma phaseDerivative_sub {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f-g) x = phaseDerivative f x - phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_sub hf hg]
  rfl

lemma phaseDerivative_const_smul {f : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    phaseDerivative (c • f) x = c • phaseDerivative f x := by
  unfold phaseDerivative
  rw [fderiv_const_smul hf]
  rfl

lemma atlasPhase_in_chart_differentiable (q p : M) (ξ : SmallModes.Base)
    {a : M} (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    DifferentiableAt ℝ (atlasPhase q ξ ∘ (coordinateChart p).symm) (coordinateChart p a) := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have ht := ((coordinateTransition_smoothOn q p) _ hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact (phaseLinear ξ).differentiableAt.comp _ (ht.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate displacement sumDisplacement)



lemma nonzeroPhaseSum_eq_quadraticFamily {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Field n) :
    nonzeroPhaseSum τ φ Z = fun p => ∑ l : QuadraticLabel ι,
      displacement τ (quadraticPhase φ l) (quadraticAmplitude τ φ Z l) p := by
  funext p
  unfold nonzeroPhaseSum
  rw [Fintype.sum_sum_type]
  dsimp only [quadraticPhase, quadraticAmplitude]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j : {j : ι // j ≠ i},
        (displacement τ (fun q => φ i q - φ j q) (phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)) p +
        displacement τ (fun q => φ i q + φ j q) (phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)) p) :=
      Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_bool]
      rfl

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_smul {n : ℕ} (θ a : ℝ) (Z : Fin n → ℂ) :
    realMode θ (a • Z) = a • realMode θ Z := by
  change realPartCLM n (QuadraticMean.phase θ • (a • Z)) =
    a • realPartCLM n (QuadraticMean.phase θ • Z)
  rw [smul_comm, map_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasQuadraticTargets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported quadratic targets for the global phase expansion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasQuadraticTargetsFiberNormed_r2469d5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticTargetsFiberSpace_r2469d5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasQuadraticTargetsDualAdd_r2469d5_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsDualSmul_r2469d5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance atlasQuadraticTargetsSectionNormed_r2469d5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticTargetsSectionSpace_r2469d5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem globalQuadraticTarget_expansion (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
      (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a)) x) =
    A.tensorPlaneRestore (fun k x => ∑ l : RealModes.QuadraticLabel ι,
      QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ k l))
        (A.globalQuadraticTarget τ φ Z hφ hZ k l) x) := by
  congr 1
  funext k x
  rw [RealModes.nonzeroPhaseSum_eq_quadraticFamily]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (A.planeWeight k x)^2 • QuadraticMean.realMode
    (RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l x / τ)
    (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
      (fun a => A.vectorPlaneRead k (Z a)) l x) = _
  simp only [QuadraticMean.displacement,coordinatePhase,globalQuadraticPhase,
    Function.comp_apply,LinearIsometryEquiv.apply_symm_apply,globalQuadraticTarget]
  exact (realMode_smul _ _ _).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticPhaseCatalog
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All quadratic phases generated by a fixed finite stock remain in one
fixed finite stock, independently of the number of repeated grid labels. -/
noncomputable section
open scoped BigOperators ContDiff
namespace ClosedSurfaceR4.RealModes

lemma quadraticPhase_mem_catalog {ι : Type*} (Γ : Finset (SmallModes.Base → ℝ))
    (φ : ι → SmallModes.Base → ℝ) (hφ : ∀ i, φ i ∈ Γ) (l : QuadraticLabel ι) :
    quadraticPhase φ l ∈ quadraticPhaseCatalog Γ := by
  classical
  rcases l with i | ⟨i,j,b⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨φ i,hφ i,rfl⟩))
  · cases b with
    | false =>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(φ i,φ j),Finset.mem_product.mpr ⟨hφ i,hφ j⟩,rfl⟩)
    | true =>
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(φ i,φ j),Finset.mem_product.mpr ⟨hφ i,hφ j⟩,rfl⟩))

lemma quadraticPhaseCatalog_smooth (Γ : Finset (SmallModes.Base → ℝ))
    (hΓ : ∀ f ∈ Γ, ContDiff ℝ ∞ f) :
    ∀ f ∈ quadraticPhaseCatalog Γ, ContDiff ℝ ∞ f := by
  classical
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
      exact contDiff_const.mul (hΓ g hg)
    · obtain ⟨⟨g,h⟩,hp,rfl⟩ := Finset.mem_image.mp hf
      exact (hΓ g (Finset.mem_product.mp hp).1).sub (hΓ h (Finset.mem_product.mp hp).2)
  · obtain ⟨⟨g,h⟩,hp,rfl⟩ := Finset.mem_image.mp hf
    exact (hΓ g (Finset.mem_product.mp hp).1).add (hΓ h (Finset.mem_product.mp hp).2)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseCatalog
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite catalogs for the actual restored global grid phases and
their readings in every atlas chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restored_linear_phase_mem_catalog (V : Finset SmallModes.Base)
    (i : A.centers) {v : SmallModes.Base} (hv : v ∈ V) :
    restore (i : M) (A.outer i) (phaseLinear v ∘ planeCoordinateIsometry) ∈
      A.linearPhaseCatalog V := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩

lemma linearPhaseCatalog_smooth (V : Finset SmallModes.Base) :
    ∀ f ∈ A.linearPhaseCatalog V, ContMDiff planeModel 𝓘(ℝ) ∞ f := by
  classical
  intro f hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hi
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((phaseLinear v).contDiff.comp planeCoordinateIsometry.contDiff)

lemma globalQuadraticPhase_mem_catalog (V : Finset SmallModes.Base)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → M → ℝ)
    (hφ : ∀ a, φ a ∈ A.linearPhaseCatalog V) (k : A.centers)
    (l : RealModes.QuadraticLabel ι) :
    coordinatePhase (A.globalQuadraticPhase φ k l) ∈ A.localQuadraticPhaseCatalog V k := by
  classical
  have he : coordinatePhase (A.globalQuadraticPhase φ k l) =
      RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l := by
    funext x
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  apply RealModes.quadraticPhase_mem_catalog
  intro a
  exact Finset.mem_image.mpr ⟨φ a,hφ a,rfl⟩

variable [CompactSpace M]

lemma localQuadraticPhaseCatalog_smooth (V : Finset SmallModes.Base) (k : A.centers) :
    ∀ f ∈ A.localQuadraticPhaseCatalog V k, ContDiff ℝ ∞ f := by
  classical
  apply RealModes.quadraticPhaseCatalog_smooth
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  exact A.vectorPlaneRead_smooth k (A.linearPhaseCatalog_smooth V g hg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPureMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform positive pure-phase margin after passage to another chart
of the fixed finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {ι : Type*} [Fintype ι]

theorem finite_atlas_pure_margin (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ ∀ (h : ℝ) (s : ι → Finset Index)
      (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base)
      (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ a q, atlasActive p ψ s h a q →
        atlasGram G (p a.1) q ≠ 0 ∧ atlasSecondTensor G (p a.1) q ≠ 0 ∧
        ε*‖atlasSecondTensor G (p a.1) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (p a.1) q) (-(ξ a).2,(ξ a).1)‖) →
      ∀ a j q, atlasActive p ψ s h a q → q ∈ tsupport (ψ j) →
        e*‖atlasSecondTensor G (p j) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (p j) q)
            (-(atlasPhaseCovector (p a.1) (p j) (ξ a) q).2,
              (atlasPhaseCovector (p a.1) (p j) (ξ a) q).1)‖ := by
  obtain ⟨d,L,hd,hL,hbound⟩ := finite_atlas_transition_bounds p ψ hsource hcompact
  let e := d^2*ε/(4*L^2)
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hd) hε)
    (mul_pos (by norm_num) (sq_pos_of_pos hL))
  refine ⟨e,he,?_⟩
  intro h s ξ G hG hlocal a j q ha hq
  have hqa : q ∈ tsupport (ψ a.1) :=
    refinedCutoff_tsupport_outer (p a.1) (ψ a.1) (s a.1) h a.2.1 ha.2
  have hap : q ∈ (coordinateChart (p a.1)).source := by
    rw [coordinateChart_source]
    exact hsource a.1 hqa
  have hjp : q ∈ (coordinateChart (p j)).source := by
    rw [coordinateChart_source]
    exact hsource j hq
  have hc := hbound j a.1 (coordinateChart (p j) q) ⟨q,⟨hq,hqa⟩,rfl⟩
  have hl := hlocal a q ha
  exact (actual_phase_margin_at hG (p a.1) (p j) hjp hap (ξ a)
    hd hL hε hl.1 hc.1 hc.2 hl.2.1 hl.2.2).2.1

lemma atlasPhaseCovector_smul (q p : M) (ξ : SmallModes.Base) (w : ℝ) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    atlasPhaseCovector q p (w • ξ) a = w • atlasPhaseCovector q p ξ a := by
  have he : atlasPhase q (w • ξ) = w • atlasPhase q ξ := by
    funext z
    simp only [atlasPhase,Function.comp_apply,phaseLinear_apply,Prod.smul_fst,
      Prod.smul_snd,smul_eq_mul,Pi.smul_apply]
    ring
  unfold atlasPhaseCovector
  rw [he]
  change phaseDerivative (w • (atlasPhase q ξ ∘ (coordinateChart p).symm))
    (coordinateChart p a) = _
  exact phaseDerivative_const_smul (atlasPhase_in_chart_differentiable q p ξ hap haq) w

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledMetricQuadraticTargets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric quadratic coefficients have size delta squared when the
oscillatory amplitudes have size delta times their wavelength. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

theorem scaled_quadraticAmplitude_bound {n : ℕ} {ι : Type*} {U : Set Base}
    (hU : IsOpen U) {φ : ι → Base → ℝ} {Z : ι → Field n}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) U) (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    {s τ δ A P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hP : 0 ≤ P) (m : ℕ)
    (hb : ∀ i, WeightedBound U s (m + 1) (A * (δ * τ)) (Z i))
    (hp : ∀ i v, ‖v‖ ≤ 1 → WeightedBound U s m P (coordDeriv v (φ i)))
    (l : QuadraticLabel ι) :
    WeightedBound U s m (δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2))
      (quadraticAmplitude τ φ Z l) := by
  have hh (i j : ι) := weighted_phaseCrossTensor hU hτ hs hτs
    (show 0 ≤ A * (δ * τ) by positivity) (show 0 ≤ A * (δ * τ) by positivity) hP
    (hφ i) (hφ j) (hZ i) (hZ j) (hb i) (hb j) (hp i) (hp j)
  have he : (n : ℝ) * (2 ^ m * ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ) *
      ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ)) =
      δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2) := by
    field_simp [hτ.ne']
  rcases l with i | ⟨i,j,b⟩
  · change WeightedBound U s m _ (phasePlusTensor τ (φ i) (φ i) (Z i) (Z i))
    simpa only [he] using (hh i i).1
  · cases b
    · simpa only [quadraticAmplitude, Bool.false_eq_true, ↓reduceIte, he] using (hh i j).1
    · simpa only [quadraticAmplitude, ↓reduceIte, he] using (hh i j).2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CutoffQuadraticBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoff multiplication preserves the delta-squared quadratic estimate. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma cutoff_square_complex_bound {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedBound univ s m D (fun x => ((χ x * χ x : ℝ) : ℂ)) := by
  let C := supportedWeightedSeminorm K 1 m χ
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨2^m*C*C,by positivity,?_⟩
  intro s hs hs1
  have hb : WeightedBound univ s m C χ :=
    (weightedBound_of_supportedSeminorm 1 m χ).shrink_scale hs.le hs1
  have hχc : ContDiffOn ℝ ∞ (fun x => (χ x : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn χ.contDiff.contDiffOn
  have hbc := QuadraticMean.weighted_real_complex isOpen_univ.uniqueDiffOn hs.le hC χ.contDiff.contDiffOn hb
  have hm : WeightedBound univ s m (2^m*C*C) (fun x => (χ x : ℂ)*(χ x : ℂ)) :=
    WeightedBound.mul isOpen_univ.uniqueDiffOn hs.le hC hC hχc hχc hbc hbc
  simpa only [Complex.ofReal_mul] using hm

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticOverlapSupports
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance overlapTargetsFiberNormed_r2469d5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_r2469d5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_r2469d5_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r2469d5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance overlapTargetsSectionNormed_r2469d5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_r2469d5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma quadraticOverlapCompact_subset (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    (A.quadraticOverlapCompact S hS k l : Set JetPolynomial.Base) ⊆ A.chartWeightCompact k := by
  rintro x ⟨p,hp,rfl⟩
  exact ⟨p,hp.1,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GlobalPhaseGerms
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On intersecting weight supports, restored global linear phases have
the same germs and covectors as the actual manifold coordinate phases. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRead_eventually_comp_coordinateInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : M → V) (k : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight k), A.outer k =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight k)) :
    A.vectorPlaneRead k F =ᶠ[𝓝 (coordinateChart (k : M) p)]
      F ∘ (coordinateChart (k : M)).symm := by
  let x := planeCoordinateIsometry (chart (k : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (k : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support k hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (k : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (k : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer k (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (k : M)).target :=
    ((chart (k : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (k : M)).map_source hpS)
  change ∀ᶠ z in 𝓝 x, A.vectorPlaneRead k F z = F ((coordinateChart (k : M)).symm z)
  filter_upwards [ho,htarget] with z hz htgt
  change localize (k : M) (A.outer k) F (planeCoordinateIsometry.symm z) = _
  rw [localize,indicator_of_mem htgt]
  change A.outer k (inv z)^2 • F (inv z) = _
  rw [hz,one_pow,one_smul]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RestoredPhaseGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual restored phases inherit quantitative margins on their
original support intersections. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restoredLinearPhase_read_phaseDerivative (i k : A.centers) (ξ : SmallModes.Base)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hpi : p ∈ tsupport (A.weight i)) (hpk : p ∈ tsupport (A.weight k)) :
    phaseDerivative (A.vectorPlaneRead k
      (restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry)))
      (coordinateChart (k : M) p) = atlasPhaseCovector (i : M) (k : M) ξ p := by
  have hi : restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry) =ᶠ[𝓝 p]
      atlasPhase (i : M) ξ := by
    filter_upwards [houter i p hpi,
      (chart (i : M)).open_source.mem_nhds (A.weight_support i hpi)] with x ho hx
    rw [restore,indicator_of_mem hx,ho,one_smul]
    rfl
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hc := (coordinateChart (k : M)).continuousAt_symm
    ((coordinateChart (k : M)).map_source hpK)
  have ht : Tendsto (coordinateChart (k : M)).symm
      (𝓝 (coordinateChart (k : M) p)) (𝓝 p) := by
    simpa only [ContinuousAt,(coordinateChart (k : M)).left_inv hpK] using hc
  have he := (A.vectorPlaneRead_eventually_comp_coordinateInverse
    (restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry)) k
      (houter k) hpk).trans (hi.comp_tendsto ht)
  unfold phaseDerivative atlasPhaseCovector
  rw [he.fderiv_eq (𝕜 := ℝ)]
  rfl

variable [CompactSpace M]

theorem restored_quadratic_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι → A.centers) (ξ : ι → SmallModes.Base) (S : ι → Set M)
    (hS : ∀ a, IsClosed (S a)) (hSi : ∀ a, S a ⊆ tsupport (A.weight (i a)))
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (F : M → Space) {ε : ℝ}
    (hpure : ∀ a k p, p ∈ S a → p ∈ tsupport (A.weight k) →
      ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)‖ ≤
        ‖secondQuadratic
          (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
          (-(atlasPhaseCovector (i a : M) (k : M) (ξ a) p).2,
            (atlasPhaseCovector (i a : M) (k : M) (ξ a) p).1)‖)
    (hpairs : ∀ a b k p, a ≠ b → p ∈ S a → p ∈ S b → p ∈ tsupport (A.weight k) →
      let B := realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)
      let u := atlasPhaseCovector (i a : M) (k : M) (ξ a) p
      let v := atlasPhaseCovector (i b : M) (k : M) (ξ b) p
      ε*‖B‖ ≤ ‖secondQuadratic B (-(u+v).2,(u+v).1)‖ ∧
      ε*‖B‖ ≤ ‖secondQuadratic B (-(u-v).2,(u-v).1)‖) :
    let φ := fun a => restore (i a : M) (A.outer (i a)) (phaseLinear (ξ a) ∘ planeCoordinateIsometry)
    ∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖ ≤
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (-(phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).2,
            (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).1)‖ := by
  intro φ k l y hy
  change y ∈ planeCoordinateIsometry '' ((chart (k : M)) ''
    (tsupport (A.weight k) ∩ globalQuadraticSupport S l)) at hy
  rcases hy with ⟨_,⟨p,⟨hpk,hpl⟩,rfl⟩,rfl⟩
  have he : coordinatePhase (A.globalQuadraticPhase φ k l) =
      quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l := by
    funext x
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  change ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
    (coordinateChart (k : M) p)‖ ≤
    ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
      (coordinateChart (k : M) p))
      (-(phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l)
          (coordinateChart (k : M) p)).2,
        (phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l)
          (coordinateChart (k : M) p)).1)‖
  have hd (a : ι) : DifferentiableAt ℝ (A.vectorPlaneRead k (φ a))
      (coordinateChart (k : M) p) := by
    have hs := A.vectorPlaneRead_smooth k (restore_smooth (i a : M) (A.outer_smooth (i a))
      (A.outer_support (i a)) ((phaseLinear (ξ a)).contDiff.comp planeCoordinateIsometry.contDiff))
    exact hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _
  have hder (a : ι) (ha : p ∈ S a) :
      phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) =
        atlasPhaseCovector (i a : M) (k : M) (ξ a) p :=
    A.restoredLinearPhase_read_phaseDerivative (i a) k (ξ a) houter (hSi a ha) hpk
  rcases l with a | ⟨a,b,c⟩
  · change ε*‖_‖ ≤ ‖secondQuadratic _
      (-(phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (φ a)) _).2,
        (phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (φ a)) _).1)‖
    rw [phaseDerivative_const_smul (hd a) 2,hder a hpl,norm_secondQuadratic_rotated_smul]
    have hh := hpure a k p hpl hpk
    nlinarith [norm_nonneg (secondQuadratic
      (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
      (-(atlasPhaseCovector (i a : M) (k : M) (ξ a) p).2,
        (atlasPhaseCovector (i a : M) (k : M) (ξ a) p).1))]
  · have hh := hpairs a b.1 k p b.2.symm hpl.1 hpl.2 hpk
    cases c
    · change ε*‖_‖ ≤ ‖secondQuadratic _
        (-(phaseDerivative (A.vectorPlaneRead k (φ a)+A.vectorPlaneRead k (φ b.1)) _).2,
          (phaseDerivative (A.vectorPlaneRead k (φ a)+A.vectorPlaneRead k (φ b.1)) _).1)‖
      rw [phaseDerivative_add (hd a) (hd b.1),hder a hpl.1,hder b.1 hpl.2]
      exact hh.1
    · change ε*‖_‖ ≤ ‖secondQuadratic _
        (-(phaseDerivative (A.vectorPlaneRead k (φ a)-A.vectorPlaneRead k (φ b.1)) _).2,
          (phaseDerivative (A.vectorPlaneRead k (φ a)-A.vectorPlaneRead k (φ b.1)) _).1)‖
      rw [phaseDerivative_sub (hd a) (hd b.1),hder a hpl.1,hder b.1 hpl.2]
      exact hh.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GoodSmoothingAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_chart_symm (F : M → Space) (p : M) (x : SmallModes.Base) :
    coordinateMap F p x = spaceCoordinates (F ((chart p).symm (planeCoordinateIsometry.symm x))) := rfl

variable [T2Space M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [T2Space M] [CompactSpace M] in
/-- Locally constant outer cutoffs identify the entire coordinate germ on
the original weight support, and hence every derivative used by the phases. -/
lemma vectorPlaneRead_eventually_coordinateMap
    (F : M → Space) (i : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))] coordinateMap F (i : M) := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (i : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support i hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (i : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (i : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (i : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer i (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (i : M)).target :=
    ((chart (i : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (i : M)).map_source hpS)
  filter_upwards [ho,htarget] with z hz htgt
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm z)) = _
  rw [localize,indicator_of_mem htgt]
  change spaceCoordinates (A.outer i (inv z)^2 • F (inv z)) = _
  rw [hz,one_pow,one_smul]
  exact (coordinateMap_chart_symm F (i : M) z).symm

end SmoothingAtlas

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridRestoredGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normal margins for the restored phases selected on a
variable grid in one fixed atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry PhaseGrid JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma gridPhaseLabel_injective (s : A.centers → Finset Index) :
    Function.Injective (A.gridPhaseLabel (s := s)) := by
  rintro ⟨i,a,j⟩ ⟨k,b,l⟩ h
  have hik : i = k := congrArg Prod.fst h
  subst k
  have hab : a = b := Subtype.ext (congrArg (fun x => x.2.1) h)
  have hjl : j = l := congrArg (fun x => x.2.2) h
  subst b
  subst l
  rfl

theorem grid_restored_quadratic_margin
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ e : ℝ, 0 < e ∧ ∀ (h : ℝ) (s : A.centers → Finset Index)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ), (∀ a, 1 ≤ w a) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s h a p →
        atlasGram G (a.1 : M) p ≠ 0 ∧ atlasSecondTensor G (a.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor G (a.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s h κ ξ w G →
      ∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact
        (A.gridPhaseSupport h (s := s)) (fun _ => isClosed_tsupport _) k l) : Set SmallModes.Base) →
        e*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) y‖ ≤
          ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) y)
            (-(phaseDerivative (coordinatePhase
              (A.globalQuadraticPhase (A.gridRestoredPhase ξ w (s := s)) k l)) y).2,
              (phaseDerivative (coordinatePhase
                (A.globalQuadraticPhase (A.gridRestoredPhase ξ w (s := s)) k l)) y).1)‖ := by
  classical
  have hsource (i : A.centers) : tsupport (A.weight i) ⊆ (chartAt Plane (i : M)).source :=
    by simpa only [chart_source] using A.weight_support i
  obtain ⟨e,he,htransfer⟩ := finite_atlas_pure_margin
    (fun i : A.centers => (i : M)) A.weight hsource
    (fun i => HasCompactSupport.of_compactSpace (A.weight i)) hε
  refine ⟨min e κ,lt_min he hκ,?_⟩
  intro h s ξ w hw G hG hlocal hpairs
  have hlocalw (a : AtlasCellPhase (ι := A.centers)) (p : M)
      (ha : atlasActive (fun i : A.centers => (i : M)) A.weight s h a p) :
      atlasGram G (a.1 : M) p ≠ 0 ∧ atlasSecondTensor G (a.1 : M) p ≠ 0 ∧
      ε*‖atlasSecondTensor G (a.1 : M) p‖ ≤
        ‖secondQuadratic (atlasSecondTensor G (a.1 : M) p)
          (-(w a • ξ a).2,(w a • ξ a).1)‖ := by
    obtain ⟨hg,hb,hm⟩ := hlocal a p ha
    refine ⟨hg,hb,?_⟩
    rw [norm_secondQuadratic_rotated_smul]
    have hw2 : 1 ≤ (w a)^2 := by nlinarith [hw a]
    have hn := norm_nonneg
      (secondQuadratic (atlasSecondTensor G (a.1 : M) p) (-(ξ a).2,(ξ a).1))
    nlinarith
  have hS (a : A.GridPhaseIndex s) : A.gridPhaseSupport h a ⊆ tsupport (A.weight a.1) :=
    refinedCutoff_tsupport_outer (a.1 : M) (A.weight a.1) (s a.1) h a.2.1.val
  have hactive (a : A.GridPhaseIndex s) (p : M) (ha : p ∈ A.gridPhaseSupport h a) :
      atlasActive (fun i : A.centers => (i : M)) A.weight s h (A.gridPhaseLabel a) p :=
    ⟨a.2.1.property,ha⟩
  have hB (k : A.centers) (p : M) (hp : p ∈ tsupport (A.weight k)) :
      realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) (coordinateChart (k : M) p) =
        atlasSecondTensor G (k : M) p :=
    (realSecondTensor_eventuallyEq
      (A.vectorPlaneRead_eventually_coordinateMap G k (houter k) hp)).eq_of_nhds
  apply A.restored_quadratic_margin (fun a : A.GridPhaseIndex s => a.1)
    (fun a => w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a))
    (A.gridPhaseSupport h) (fun _ => isClosed_tsupport _) hS houter G
  · intro a k p ha hp
    rw [hB k p hp]
    exact (mul_le_mul_of_nonneg_right (min_le_left e κ) (norm_nonneg _)).trans
      (htransfer h s (fun a => w a • ξ a) G hG hlocalw (A.gridPhaseLabel a) k p
        (hactive a p ha) hp)
  · intro a b k p hab ha hb hp
    have has := hsource a.1 (hS a ha)
    have hbs := hsource b.1 (hS b hb)
    have hks := hsource k hp
    have has' : p ∈ (coordinateChart (a.1 : M)).source := by
      simpa only [coordinateChart_source] using has
    have hbs' : p ∈ (coordinateChart (b.1 : M)).source := by
      simpa only [coordinateChart_source] using hbs
    have hks' : p ∈ (coordinateChart (k : M)).source := by
      simpa only [coordinateChart_source] using hks
    dsimp only
    rw [hB k p hp,
      atlasPhaseCovector_smul (a.1 : M) (k : M) _ _ hks' has',
      atlasPhaseCovector_smul (b.1 : M) (k : M) _ _ hks' hbs']
    have hh := hpairs (A.gridPhaseLabel a) (A.gridPhaseLabel b) k p
      (fun heq => hab (A.gridPhaseLabel_injective s heq)) (hactive a p ha) (hactive b p hb) hp
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right e κ) (norm_nonneg _)).trans hh.1,
      (mul_le_mul_of_nonneg_right (min_le_right e κ) (norm_nonneg _)).trans hh.2.1⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricForcedFactorBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial geometric factors and the number of actual quadratic labels. -/
noncomputable section
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.RealModes

theorem card_quadraticLabel_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fintype.card (QuadraticLabel ι) ≤ Fintype.card ι + 2*(Fintype.card ι)^2 := by
  change Fintype.card (ι ⊕ (Σ i : ι, {j : ι // j ≠ i} × Bool)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sigma]
  apply Nat.add_le_add_left
  calc
    (∑ i : ι, Fintype.card ({j : ι // j ≠ i} × Bool)) ≤
        ∑ _i : ι, Fintype.card ι*2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_prod,Fintype.card_bool]
      exact Nat.mul_le_mul_right 2 (Fintype.card_subtype_le _)
    _ = 2*(Fintype.card ι)^2 := by simp <;> ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticTargetBudget
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic target constant is polynomial in the amplitude and phase
budgets, with the fixed cutoff constant kept explicit. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem cutoff_quadratic_bound_explicit {ι : Type*} {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedBound univ s m D (fun x => ((χ x * χ x : ℝ) : ℂ)))
    (A P : ℝ) :
    ∀ (τ s δ : ℝ)
      (φ : ι → SmallModes.Base → ℝ) (Z : ι → SmallModes.Field 4),
      (∀ a, ContDiff ℝ ∞ (φ a)) → (∀ a, ContDiff ℝ ∞ (Z a)) →
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A → 0 ≤ P →
      (∀ a, WeightedBound univ s (m+1) (A*(δ*τ)) (Z a)) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedBound univ s m P (SmallModes.coordDeriv v (φ a))) →
      ∀ l : RealModes.QuadraticLabel ι,
      WeightedBound univ s m (quadraticTargetBudget m D A P*δ^2)
        (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) := by
  let C := 4 * 2^m * ((1+2^m*P)*A)^2
  intro τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hb hp l
  have hquad : WeightedBound univ s m (δ^2*C) (RealModes.quadraticAmplitude τ φ Z l) :=
    RealModes.scaled_quadraticAmplitude_bound isOpen_univ (fun a => (hφ a).contDiffOn)
      (fun a => (hZ a).contDiffOn) hτ hs hτs hδ hA hP m hb hp l
  have hcs : ContDiffOn ℝ ∞ (fun x => ((χ x * χ x : ℝ) : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (χ.contDiff.contDiffOn.mul χ.contDiff.contDiffOn)
  have hqs : ContDiffOn ℝ ∞ (RealModes.quadraticAmplitude τ φ Z l) univ :=
    (RealModes.quadraticAmplitude_smooth hφ hZ τ l).contDiffOn
  have hout : WeightedBound univ s m (2^m*D*(δ^2*C))
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) :=
    SmallModes.weighted_smul_field isOpen_univ.uniqueDiffOn hs hD
      (by dsimp [C] <;> positivity) hcs hqs (hd s hs hs1) hquad
  have he : (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) =
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) := by
    funext x j
    rw [Pi.smul_apply,Pi.smul_apply,pow_two]
    rfl
  rw [he]
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [quadraticTargetBudget,C]
  ring

lemma quadraticTargetBudget_polynomial (m : ℕ) (D A P : ℝ → ℝ)
    (hD : RealModes.HasPolynomialBound D) (hA : RealModes.HasPolynomialBound A)
    (hP : RealModes.HasPolynomialBound P) :
    RealModes.HasPolynomialBound (fun x => quadraticTargetBudget m (D x) (A x) (P x)) := by
  unfold quadraticTargetBudget
  repeat first
    | exact hD
    | exact hA
    | exact hP
    | apply RealModes.HasPolynomialBound.add
    | apply RealModes.HasPolynomialBound.mul
    | apply RealModes.HasPolynomialBound.pow
    | (apply RealModes.polynomialBound_const; positivity)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CardinalityQuadraticCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global quadratic cancellation with explicit polynomial dependence on
the number of free phases. Atlas constants precede all finite label types. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance cardinalityQuadraticFiberNormed_r2469d5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cardinalityQuadraticFiberSpace_r2469d5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cardinalityQuadraticDualAdd_r2469d5_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance cardinalityQuadraticDualSmul_r2469d5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance cardinalityQuadraticSectionNormed_r2469d5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cardinalityQuadraticSectionSpace_r2469d5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma quadratic_family_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (f : A.centers → RealModes.QuadraticLabel ι → ℝ) (hf : ∀ k l, f k l ≤ B) :
    (∑ k : A.centers, ∑ l, f k l) ≤
      (Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*B := by
  have hc : Fintype.card (RealModes.QuadraticLabel ι) ≤ n+2*n^2 := by
    apply (RealModes.card_quadraticLabel_le ι).trans
    gcongr
  have hcr : (Fintype.card (RealModes.QuadraticLabel ι) : ℝ) ≤ (n : ℝ)+2*(n : ℝ)^2 := by
    exact_mod_cast hc
  calc
    (∑ k : A.centers, ∑ l, f k l) ≤ ∑ _k : A.centers, ∑ _l : RealModes.QuadraticLabel ι, B :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hf k l))
    _ = (Fintype.card A.centers : ℝ)*(Fintype.card (RealModes.QuadraticLabel ι) : ℝ)*B := by simp <;> ring
    _ ≤ _ := by gcongr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CatalogGlobalQuadraticCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual global quadratic correction with explicit polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.catalogGlobalQuadraticDualAdd
local instance catalogGlobalQuadraticFiberNormed_r2469d5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogGlobalQuadraticFiberSpace_r2469d5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance catalogGlobalQuadraticDualSmul_r2469d5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance catalogGlobalQuadraticSectionNormed_r2469d5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance catalogGlobalQuadraticSectionSpace_r2469d5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem catalog_global_quadratic_correction
    (V : Finset SmallModes.Base) {ε b D : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B α β : ℕ → ℝ → ℝ)
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
    (hα : ∀ m, RealModes.HasPolynomialBound (α m))
    (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], ∀ n : ℕ, Fintype.card ι ≤ n →
      ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (_hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (S : ι → Set M) (hS : ∀ a, IsClosed (S a)),
      (∀ a, φ a ∈ A.linearPhaseCatalog V) → (∀ a, tsupport (Z a) ⊆ S a) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        ε*‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖ ≤
          ‖PhaseGeometry.secondQuadratic
            (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
            (-(phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).2,
              (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).1)‖) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
        (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
        (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) y))) := by
  classical
  obtain ⟨e,C,hC,hcancel⟩ := A.finite_catalog_atlas_cancellation
    (A.localQuadraticPhaseCatalog V) (A.localQuadraticPhaseCatalog_smooth V)
    hε hb hD hDB B hB hB1 q
  choose T hT ht using fun (k : A.centers) m =>
    cutoff_square_complex_bound (A.supportedPlaneWeight k) m
  let T₀ := fun m => ∑ k : A.centers, T k m
  have hT₀ (m : ℕ) : 0 ≤ T₀ m := Finset.sum_nonneg (fun k _ => hT k m)
  have hTT (k : A.centers) (m : ℕ) : T k m ≤ T₀ m :=
    Finset.single_le_sum (fun i _ => hT i m) (Finset.mem_univ k)
  let N := fun m => PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m
  let H := fun m x => (Fintype.card A.centers : ℝ)*(C m*x^(e m))*
    quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)
  have hH (m : ℕ) : RealModes.HasPolynomialBound (H m) :=
    ((RealModes.polynomialBound_const (Nat.cast_nonneg _)).mul
      ((RealModes.polynomialBound_const (zero_le_one.trans (hC m))).mul
        (RealModes.polynomialBound_id.pow (e m)))).mul
      (quadraticTargetBudget_polynomial (N m) _ _ _
        (RealModes.polynomialBound_const (hT₀ _)) (hα _) (hβ _))
  choose d E hE hbound using hH
  refine ⟨d,E,hE,?_⟩
  intro ι inst dec n hn x hx F hF φ Z hφ hZ S hS hcat hSZ hImm hnormal hrel hgram
    τ δ s hτ hs hτs hs1 hδ hFj hz hp
  let : DecidableEq ι := dec
  let K := fun k l => modeSupport (A.quadraticOverlapCompact S hS k l)
  let target := A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ
  have hα0 (m : ℕ) : 0 ≤ α m x := by
    obtain ⟨_,_,_,hh⟩ := hα m
    exact (hh x hx).1
  have hβ0 (m : ℕ) : 0 ≤ β m x := by
    obtain ⟨_,_,_,hh⟩ := hβ m
    exact (hh x hx).1
  have htarget (k : A.centers) (l : RealModes.QuadraticLabel ι) (m : ℕ) :
      supportedWeightedSeminorm (K k l) s m (target k l) ≤
        quadraticTargetBudget m (T₀ m) (α m x) (β m x)*δ^2 := by
    have hcut : ∀ t : ℝ, 0 < t → t ≤ 1 → WeightedEstimates.WeightedBound univ t m (T₀ m)
        (fun y => ((A.supportedPlaneWeight k y*A.supportedPlaneWeight k y : ℝ) : ℂ)) :=
      fun t htpos ht1 => (ht k m t htpos ht1).mono_const (hTT k m)
    apply supportedSeminorm_le_of_weightedBound hs (by
      have hTn := hT₀ m
      dsimp [quadraticTargetBudget]
      positivity)
    exact cutoff_quadratic_bound_explicit (A.supportedPlaneWeight k) m (hT₀ m) hcut
      (α m x) (β m x) τ s δ (fun a => A.vectorPlaneRead k (φ a))
      (fun a => A.vectorPlaneRead k (Z a))
      (fun a => A.vectorPlaneRead_smooth k (hφ a))
      (fun a => A.vectorPlaneRead_smooth k (hZ a)) hτ hs hτs hs1 hδ
      (hα0 m) (hβ0 m) (fun a => hz k a m) (fun a v hv => hp k a m v hv) l
  obtain ⟨W,hW,hv,hr⟩ := hcancel x hx F hF
    (fun k l => coordinatePhase (A.globalQuadraticPhase φ k l))
    (A.globalQuadraticPhase_mem_catalog V φ hcat) K
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    hImm hnormal hrel hgram τ s hτ hs hτs hs1 hFj target
  have hsum (m : ℕ) :
      (∑ k : A.centers, ∑ l : RealModes.QuadraticLabel ι,
        supportedWeightedSeminorm (K k l) s (N m) (target k l)) ≤
      (Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
        (quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)*δ^2) := by
    apply A.quadratic_family_sum_le hn _ _ (fun k l => htarget k l (N m))
    have ht0 := hT₀ (N m)
    dsimp [quadraticTargetBudget]
    positivity
  have hcoefficient (m : ℕ) :
      (C m*x^(e m))*(∑ k : A.centers, ∑ l : RealModes.QuadraticLabel ι,
        supportedWeightedSeminorm (K k l) s (N m) (target k l)) ≤
      δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m)) := by
    have hc0 : 0 ≤ C m*x^(e m) :=
      mul_nonneg (zero_le_one.trans (hC m)) (pow_nonneg (zero_le_one.trans hx) _)
    calc
      _ ≤ (C m*x^(e m))*((Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
          (quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)*δ^2)) :=
        mul_le_mul_of_nonneg_left (hsum m) hc0
      _ = δ^2*((n : ℝ)+2*(n : ℝ)^2)*H m x := by dsimp [H] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound m x hx).2 (by positivity)
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    exact (hv m k).mono_const (hcoefficient m)
  · intro m k
    have hh := (hr m k).mono_const (by
      have h := mul_le_mul_of_nonneg_left (hcoefficient m)
        (pow_nonneg (div_nonneg hτ.le hs.le) (q+1))
      simpa only [mul_assoc] using h)
    have he := A.globalQuadraticTarget_expansion τ φ Z hφ hZ
    have hrest : A.tensorPlaneRestore (fun i y =>
        ∑ j : RealModes.QuadraticLabel ι, QuadraticMean.displacement τ
          (coordinatePhase (A.globalQuadraticPhase φ i j)) (target i j) y) =
        A.tensorPlaneRestore (fun i y =>
        ∑ j : RealModes.QuadraticLabel ι, QuadraticMean.displacement τ
          (coordinatePhase (A.globalQuadraticPhase φ i j))
          (A.globalQuadraticTarget τ φ Z hφ hZ i j) y) := by
      congr 1
    rw [hrest] at hh
    rw [he]
    simpa only [mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridGlobalQuadraticCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual correction for the variable grid with a fixed polynomial budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGlobalQuadraticDualAdd
local instance gridGlobalQuadraticFiberNormed_r2469d5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGlobalQuadraticFiberSpace_r2469d5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridGlobalQuadraticDualSmul_r2469d5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance gridGlobalQuadraticSectionNormed_r2469d5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGlobalQuadraticSectionSpace_r2469d5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqGridPhaseIndex
theorem grid_global_quadratic_correction_oai (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (B α β : ℕ → ℝ → ℝ)
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
    (hα : ∀ m, RealModes.HasPolynomialBound (α m))
    (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ (h : ℝ) (s₀ : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ a, 1 ≤ w a) →
      (∀ a : A.GridPhaseIndex s₀, w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex s₀) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s₀ h a p →
        atlasGram F (a.1 : M) p ≠ 0 ∧ atlasSecondTensor F (a.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (a.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s₀ h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ (Z : A.GridPhaseIndex s₀ → M → Fin 4 → ℂ)
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
      (∀ a, tsupport (Z a) ⊆ A.gridPhaseSupport h a) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
        (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
        (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
              RealModes.nonzeroPhaseSum τ
                (fun a => A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a))
                (fun a => A.vectorPlaneRead k (Z a)) y))) := by
  classical
  obtain ⟨e,he,hmargin⟩ := A.grid_restored_quadratic_margin houter hε hκ
  let D := max 1 (max D₀ (e*b)⁻¹)
  have hD : 1 ≤ D := le_max_left _ _
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDB : (e*b)⁻¹ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨d,E,hE,hcancel⟩ := A.catalog_global_quadratic_correction V he hb hD hDB
    B α β hB hB1 hα hβ q
  refine ⟨d,E,hE,?_⟩
  intro h s₀ ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    τ δ s hτ hs hτs hs1 hδ hFj Z hZ hSZ hz hp
  have hcat (a : A.GridPhaseIndex s₀) : A.gridRestoredPhase (s := s₀) ξ w a ∈ A.linearPhaseCatalog V :=
    A.restored_linear_phase_mem_catalog V a.1 (hV a)
  have hφ (a : A.GridPhaseIndex s₀) : ContMDiff planeModel 𝓘(ℝ) ∞ (A.gridRestoredPhase (s := s₀) ξ w a) :=
    A.linearPhaseCatalog_smooth V _ (hcat a)
  have hsub (k : A.centers) (l : RealModes.QuadraticLabel (A.GridPhaseIndex s₀)) :
      (modeSupport (A.quadraticOverlapCompact (A.gridPhaseSupport h)
        (fun _ => isClosed_tsupport _) k l) : Set SmallModes.Base) ⊆
        modeSupport (A.chartWeightCompact k) :=
    Set.image_mono (A.quadraticOverlapCompact_subset (A.gridPhaseSupport h)
      (fun _ => isClosed_tsupport _) k l)
  exact hcancel n hn x hx F hF (A.gridRestoredPhase (s := s₀) ξ w) Z hφ hZ
    (A.gridPhaseSupport h) (fun _ => isClosed_tsupport _) hcat hSZ
    (fun k l y hy => hImm k y (hsub k l hy))
    (fun k l y hy => hnormal k y (hsub k l hy))
    (hmargin h s₀ ξ w hw F hF hlocal hpairs)
    (fun k l y hy => (hgram k y (hsub k l hy)).trans hD₀)
    τ δ s hτ hs hτs hs1 hδ hFj hz hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction_oai.{u_1}
