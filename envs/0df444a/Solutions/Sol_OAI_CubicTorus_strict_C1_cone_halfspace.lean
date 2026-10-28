-- Prove2me | solution 1 for OAI.CubicTorus.strict_C1_cone_halfspace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:45:14.512706+00:00
-- url     : https://prove2.me/submissions/aee6213d-68d5-4fb9-96ce-a9e27f58bbdb

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

open scoped RealInnerProductSpace

namespace CubicTorus
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

lemma linearForm_apply_basis (L : Cover →L[ℝ] ℝ) (v : Cover) :
    L v = ∑ j : Fin 3, v j * L (EuclideanSpace.single j 1) := by
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, map_sum]
  simp

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

lemma hyperplane_volume_zero {n : Cover} (hn : ‖n‖ = 1) :
    volume {x : Cover | ⟪n, x⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n, n⟫ = 0 at hm
  rw [real_inner_self_eq_norm_sq, hn] at hm
  norm_num at hm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

lemma radialDensityWeight_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityWeight a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (radialDensityWeight_zero hr hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hh)))

lemma radialDensityWeight_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityWeight a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityWeight_tsupport hr hε)

lemma radialHeightCutoff_one {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a r) : radialHeightCutoff a r x = 1 := by
  have hnorm : ‖x - a‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by positivity : 0 < 3 * r ^ 2)).mpr
  nlinarith [norm_nonneg (x - a)]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_inner {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪n, normalGraph n g y⟫ = g y := by
  simp [normalGraph, inner_add_right, normalPlaneEmbedding_inner hn,
    inner_smul_right, hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
attribute [-instance] _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMove_hasFDerivAt (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (normalMove n f)
      (ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight n) x := by
  exact (hasFDerivAt_id x).add (hf.hasFDerivAt.smul_const n)

lemma normalMove_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMove n f) := contDiff_id.add (hf.smul_const n)

lemma normalPullback_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (normalPullback n f F) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hG := hF.comp (normalMove_contDiff n hf)
  exact (contDiff_const.add (hd.clm_apply contDiff_const)).smul hG |>.sub
    ((hd.clm_apply hG).smul contDiff_const)

lemma divergence_comp_normalMove (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) {F : Cover → Cover}
    (hF : DifferentiableAt ℝ F (normalMove n f x)) :
    divergence (fun y ↦ F (normalMove n f y)) x =
      divergence F (normalMove n f x) +
        fderiv ℝ f x (fderiv ℝ F (normalMove n f x) n) := by
  have hd := (hF.hasFDerivAt.comp x (normalMove_hasFDerivAt n hf)).fderiv
  change fderiv ℝ (fun y ↦ F (normalMove n f y)) x = _ at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPullback_divergence (n : Cover) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (normalPullback n f F) x =
      normalJacobian n f x * divergence F (normalMove n f x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := normalMove_hasFDerivAt n hfd
  have hg := (hF.differentiable (by simp)).differentiableAt (x := normalMove n f x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const n x)).const_add 1
  have hb := hdf.hasFDerivAt.clm_apply hu
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)) n (F (normalMove n f x))
  change divergence (fun y ↦ normalJacobian n f y • F (normalMove n f y) -
    fderiv ℝ f y (F (normalMove n f y)) • n) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (normalJacobian n f) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (normalJacobian n f) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ F (normalMove n f y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (F (normalMove n f y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ normalJacobian n f y • F (normalMove n f y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (F (normalMove n f y)) • n) x := hB.smul_const n
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU, divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_normalMove n hfd hg]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, zero_add,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero, smul_eq_mul]
  dsimp only [normalJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphShear_columnChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphShear a n g (normalColumnChart a n (t,y)) = normalColumnChart a n (t+g y,y) := by
  change normalColumnChart a n (t,y) +
    g (normalPlaneCoordinates n (normalColumnChart a n (t,y)-a)) • n = _
  rw [normalColumnChart_projection a hn, normalColumnChart_apply a hn,
    normalColumnChart_apply a hn, add_smul]
  abel

lemma columnShear_measurePreserving {g : Plane → ℝ} (hg : Measurable g) :
    MeasurePreserving (fun p : ℝ × Plane ↦ (p.1+g p.2, p.2)) := by
  have hs : MeasurePreserving (fun p : Plane × ℝ ↦ (p.1, p.2+g p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y ↦ (measurePreserving_add_right volume (g y)).map_eq)
  have hh := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure ℝ))).comp (hs.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))))
  simpa only [Function.comp_def, Prod.swap, Measure.volume_eq_prod] using hh

lemma graphShear_measurePreserving (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Measurable g) : MeasurePreserving (graphShear a n g) := by
  have hi : MeasurePreserving (normalColumnChart a n).symm :=
    MeasurePreserving.symm (normalColumnChart a n) (normalColumnChart_measurePreserving a n)
  have hh := (normalColumnChart_measurePreserving a n).comp
    ((columnShear_measurePreserving hg).comp hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart a n).surjective x
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact graphShear_columnChart a hn g t y

lemma graphHeightExtension_fderiv (a n : Cover) {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (x : Cover) : fderiv ℝ (graphHeightExtension a n g) x =
      (fderiv ℝ g (normalPlaneCoordinates n (x-a))).comp (normalPlaneCoordinates n) := by
  unfold graphHeightExtension
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, graphHeightExtension] using
    ((hg _).hasFDerivAt.comp x hp).fderiv

lemma graphHeightExtension_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    fderiv ℝ (graphHeightExtension a n g) x n = 0 := by
  rw [graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    normalPlaneCoordinates_normal hn, map_zero]

lemma graphShear_jacobian (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    normalJacobian n (graphHeightExtension a n g) x = 1 := by
  rw [normalJacobian, graphHeightExtension_normal a hn hg, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSublevelIndicator_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSublevelIndicator a n g (graphShear a n g x) = halfspaceIndicator n (x-a) := by
  have hheight : ⟪n, graphShear a n g x - a⟫ = ⟪n,x-a⟫ + graphHeightExtension a n g x := by
    simp only [graphShear, normalMove, add_sub_right_comm, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hp : graphHeightExtension a n g (graphShear a n g x) = graphHeightExtension a n g x :=
    congrArg g (graphShear_projection a hn g x)
  simp only [graphSublevelIndicator, Set.indicator, Set.mem_ofPred_eq, hheight, hp,
    add_lt_iff_neg_right, halfspaceIndicator]

lemma normalPullback_graph_compactSupport (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {F : Cover → Cover} (hs : HasCompactSupport F) :
    HasCompactSupport (normalPullback n (graphHeightExtension a n g) F) := by
  have hc := hs.comp_homeomorph (graphShearHomeomorph a hn hg)
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  dsimp only [Function.comp_def, graphShearHomeomorph] at hx
  have hh : F (graphShear a n g x) = 0 := hx
  simp only [Function.mem_support, not_not]
  change normalPullback n (graphHeightExtension a n g) F x = 0
  change F (normalMove n (graphHeightExtension a n g) x) = 0 at hh
  simp only [normalPullback, hh, smul_zero, map_zero, zero_smul, sub_self]

lemma graphAreaVector_pullback (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (F : Cover → Cover) (y : Plane) :
    ⟪n, normalPullback n (graphHeightExtension a n g) F (a+normalPlaneEmbedding n y)⟫ =
      ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hs : graphShear a n g (a+normalPlaneEmbedding n y) = a+normalGraph n g y := by
    simp only [graphShear, normalMove, graphHeightExtension, add_sub_cancel_left,
      normalPlaneCoordinates_embedding, normalGraph]
    abel
  rw [normalPullback, graphShear_jacobian a hn hg, one_smul, ← graphShear, hs,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    add_sub_cancel_left, normalPlaneCoordinates_embedding]
  rw [graphAreaVector, inner_sub_left]
  congr 1
  rw [show normalPlaneEmbedding n (gradient g y) =
    (normalPlaneLinearIsometry n).toContinuousLinearMap (gradient g y) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
  rfl

theorem integral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hmp : MeasurePreserving (graphShearHomeomorph a hn hg.continuous).toMeasurableEquiv :=
    graphShear_measurePreserving a hn hg.continuous.measurable
  rw [← hmp.integral_comp' (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x)]
  have he (x : Cover) : graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
      divergence F (graphShearHomeomorph a hn hg.continuous x) =
      halfspaceIndicator n (x-a) * divergence (normalPullback n (graphHeightExtension a n g) F) x := by
    change graphSublevelIndicator a n g (graphShear a n g x) * divergence F (graphShear a n g x) = _
    rw [graphSublevelIndicator_shear a hn, normalPullback_divergence n
      (graphHeightExtension_contDiff a n hg) hF,
      graphShear_jacobian a hn (hg.differentiable (by simp)), one_mul]
    rfl
  change (∫ x : Cover, graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
    divergence F (graphShearHomeomorph a hn hg.continuous x)) = _
  simp_rw [he]
  rw [integral_halfspace_divergence a hn
    (normalPullback_contDiff n (graphHeightExtension_contDiff a n hg) hF)
    (normalPullback_graph_compactSupport a hn hg.continuous hs)]
  apply integral_congr_ae
  exact Eventually.of_forall (graphAreaVector_pullback a hn (hg.differentiable (by simp)) F)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graphAreaVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ ^ 2 = 1 + ‖fderiv ℝ g y‖ ^ 2 := by
  rw [graphAreaVector, norm_sub_sq_real, hn, one_pow,
    normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn, plane_gradient_norm]
  ring

lemma graph_trace_compactSupport {X : Type*} [Zero X]
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hs : HasCompactSupport F) :
    HasCompactSupport (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  have hc := (hs.comp_homeomorph (graphShearHomeomorph a hn hg)).comp_isClosedEmbedding
    (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
  have he (y : Plane) : graphShearHomeomorph a hn hg (normalColumnChart a n (0,y)) =
      a+normalGraph n g y := by
    change graphShear a n g (normalColumnChart a n (0,y)) = _
    rw [graphShear_columnChart a hn, zero_add, normalColumnChart_apply a hn]
    rfl
  simpa only [Function.comp_def, he] using hc

lemma graphAreaVector_continuous (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphAreaVector n g) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact continuous_const.sub ((normalPlaneLinearIsometry n).continuous.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp hd))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_norm_ge {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖y‖ ≤ ‖normalGraph n g y‖ := by
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (normalGraph n g y) 0
  simpa only [normalPlaneCoordinates_graph hn, map_zero, dist_zero_right,
    NNReal.coe_one, one_mul] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma primitive_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ u in (0 : ℝ)..t, b u) := by
  have hd (t : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.continuous.intervalIntegrable 0 t) (hb.continuous.stronglyMeasurableAtFilter volume _)
    hb.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (hd t).differentiableAt,?_⟩
  simpa only [funext (fun t ↦ (hd t).deriv)] using hb

lemma intervalSmoothHat_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (a c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (intervalSmoothHat b a c) :=
  ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const)).sub
    ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const))

lemma intervalSmoothHat_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : HasDerivAt (intervalSmoothHat b a c) (b (t-a)-b (t-c)) t := by
  have hd (x : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable 0 x) (hb.stronglyMeasurableAtFilter volume _) hb.continuousAt
  change HasDerivAt (fun x : ℝ ↦ (∫ u in (0 : ℝ)..x-a, b u) -
    ∫ u in (0 : ℝ)..x-c, b u) _ _
  simpa only [Function.comp_def,mul_one,id_eq,Pi.sub_def] using
    ((hd (t-a)).comp t ((hasDerivAt_id t).sub_const a)).sub
      ((hd (t-c)).comp t ((hasDerivAt_id t).sub_const c))

lemma intervalSmoothHat_eq_integral {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : intervalSmoothHat b a c t = ∫ u in t-c..t-a, b u := by
  rw [intervalSmoothHat]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hb.intervalIntegrable 0 (t-c)) (hb.intervalIntegrable (t-c) (t-a))
  linarith

lemma intervalSmoothHat_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c) :
    tsupport (intervalSmoothHat b a c) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  rw [intervalSmoothHat_eq_integral hb]
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro u hu
  have htc : t-c ≤ t-a := by linarith
  rw [uIoc_of_le htc] at hu
  apply image_eq_zero_of_notMem_tsupport
  intro hub
  have hur := hs hub
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hl|hr
  · linarith [hu.2,hur.1]
  · linarith [hu.1,hur.2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma angularMollifier_radius_tendsto :
    Tendsto (fun n ↦ (angularMollifier n).rOut) atTop (𝓝 0) := by
  have he (n : ℕ) : (angularMollifier n).rOut = (1/8 : ℝ)*(1/((n : ℝ)+1)) := by
    dsimp [angularMollifier]; field_simp; ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_const_nhds (x := (1/8 : ℝ))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarAngularChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeScalarTest_contDiff {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) : ContDiff ℝ (⊤ : ℕ∞) (slopeScalarTest χ ψ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hP : ContDiff ℝ (⊤ : ℕ∞) planeProductCoordinates :=
    planeProductCoordinates.contDiff
  by_cases hx : (planeProductCoordinates x).1 = 0
  · have heχ : χ =ᶠ[𝓝 ((planeProductCoordinates x).1)] 0 := by
      rw [hx]
      exact notMem_tsupport_iff_eventuallyEq.mp hχ0
    have he : slopeScalarTest χ ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hP.continuous.fst.tendsto x).eventually heχ] with y hy
      simp only [slopeScalarTest,hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (hχ.contDiffAt.comp x hP.fst.contDiffAt).mul
      (hψ.contDiffAt.comp x (hP.snd.contDiffAt.div hP.fst.contDiffAt hx))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

theorem blowupNormal_weighted_saturation {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {w : BlowupNormalBundle → ℝ}
    (hiw : Integrable w ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}))
    {C : ℝ} (hC : 0 < C) (hwC : ∀ z, w z ≤ C)
    {L : ℝ}
    (hL : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z*⟪(z.2 : Cover),F z.1⟫
        ∂(ν : Measure BlowupNormalBundle)) ≤ L) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z
      ∂(ν : Measure BlowupNormalBundle)) ≤ L := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let P : ℝ := (coverLocalPerimeter A O).toReal
  let I : ℝ := ∫ z, w z ∂μ
  let B : ℝ := P+(L-I)/C
  have hmass : (∫ _ : BlowupNormalBundle, (1 : ℝ) ∂μ) = P := by
    simp only [integral_const,smul_eq_mul,mul_one,μ,P,heq,Measure.real,Measure.restrict_apply_univ]
  have hbound (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (hn : ∀ x, ‖F x‖ ≤ 1) :
      (∫ x in A, divergence F x) ≤ B := by
    let T : BlowupNormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F z.1⟫
    have hTc : Continuous T := (continuous_subtype_val.comp continuous_snd).inner
      (hF.continuous.comp continuous_fst)
    have hTb (z : BlowupNormalBundle) : |T z| ≤ 1 := blowup_test_inner_bound hn z
    have hiT : Integrable T μ := Integrable.of_bound hTc.aestronglyMeasurable 1
      (ae_of_all μ hTb)
    have hiwT : Integrable (fun z ↦ w z*T z) μ := by
      simpa only [mul_comm] using hiw.bdd_mul hTc.aestronglyMeasurable (ae_of_all μ hTb)
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) (fun z ↦ show
        w z-w z*T z ≤ C*(1-T z) from by
          have ht : 0 ≤ 1-T z := by linarith [(le_abs_self (T z)).trans (hTb z)]
          nlinarith [mul_le_mul_of_nonneg_right (hwC z) ht])
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT,integral_const_mul,integral_sub (integrable_const 1) hiT,hmass] at hh
    have hf : (∫ z, T z ∂μ) = ∫ x in A, divergence F x := by
      rw [show (∫ z, T z ∂μ) = ∫ z, T z ∂(ν : Measure BlowupNormalBundle) from ?_]
      · exact hflux F hF hs hO hn
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzF : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hO hh))
      simp only [T,hzF,inner_zero_right]
    rw [hf] at hh
    have hl := hL F hF hs hO hn
    change (∫ z, w z*T z ∂μ) ≤ L at hl
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul,div_mul_cancel₀ _ hC.ne']
    dsimp only [I]
    nlinarith
  have hB : 0 ≤ B := by
    have hh := hbound (fun _ ↦ 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa only [divergence_zero,integral_zero] using hh
  have hper : coverLocalPerimeter A O ≤ ENNReal.ofReal B := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hn
    exact ENNReal.ofReal_le_ofReal (hbound F hF hs hO hn)
  have hPB : P ≤ B := by
    simpa only [P,ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hper
  have hnon : 0 ≤ (L-I)/C := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hnon hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupComplement
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma integral_cover_divergence_zero {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, divergence F x) = 0 := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_compact_fderiv_zero (hp i) (hps i) _
  · intro i _
    exact (((hp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hps i).fderiv_apply ℝ _)

lemma integral_cover_divergence_compl {A : Set Cover} (hA : MeasurableSet A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in Aᶜ, divergence F x) = -(∫ x in A, divergence F x) := by
  have hi : Integrable (divergence F) (volume : Measure Cover) :=
    (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  have hh := integral_add_compl hA hi
  rw [integral_cover_divergence_zero hF hs] at hh
  linarith

theorem coverLocalPerimeter_compl {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
    coverLocalPerimeter Aᶜ O = coverLocalPerimeter A O := by
  have hle {A : Set Cover} (hA : MeasurableSet A) :
      coverLocalPerimeter Aᶜ O ≤ coverLocalPerimeter A O := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hnorm
    have hFn : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ -F x) := hF.neg
    have hsFn : HasCompactSupport (fun x ↦ -F x) := hs.neg
    have hOFn : tsupport (fun x ↦ -F x) ⊆ O := by
      change tsupport (-F) ⊆ O
      simpa only [tsupport_neg] using hO
    have hnFn (x) : ‖-F x‖ ≤ 1 := by simpa using hnorm x
    have he : (∫ x in Aᶜ, divergence F x) = ∫ x in A, divergence (fun y ↦ -F y) x := by
      rw [integral_cover_divergence_compl hA hF hs]
      simp only [divergence_neg,integral_neg]
    rw [he]
    exact le_iSup_of_le (fun x ↦ -F x) (le_iSup_of_le hFn (le_iSup_of_le hsFn
      (le_iSup_of_le hOFn (le_iSup_of_le hnFn le_rfl))))
  exact le_antisymm (hle hA) (by simpa only [compl_compl] using hle hA.compl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma continuous_reverseBlowupNormal : Continuous reverseBlowupNormal :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

lemma reverseBlowupNormal_spatial_mass (ν : FiniteMeasure BlowupNormalBundle)
    {O : Set Cover} (hO : MeasurableSet O) :
    (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply continuous_reverseBlowupNormal.measurable
    (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} from hO.preimage measurable_fst)]
  rfl

lemma reverseBlowupNormal_flux {A O : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hFO : tsupport F ⊆ O) (hFn : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle)) =
      ∫ x in Aᶜ, divergence F x := by
  rw [FiniteMeasure.toMeasure_map,integral_map continuous_reverseBlowupNormal.measurable.aemeasurable
    (continuous_blowupFluxTest hF.continuous).aestronglyMeasurable]
  change (∫ z, ⟪-(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = _
  simp_rw [inner_neg_left,integral_neg]
  rw [integral_cover_divergence_compl hA hF hs,hflux F hF hs hFO hFn]

lemma coverLocalPerimeter_normal_compl {A O : Set Cover} (hA : MeasurableSet A)
    (hO : MeasurableSet O) {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O}) :
    coverLocalPerimeter Aᶜ O =
      (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [coverLocalPerimeter_compl hA,reverseBlowupNormal_spatial_mass ν hO,heq]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarEssentialBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measureSupport_local_ae_mono {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {A B O : Set X} {p : X}
    (hO : O ∈ 𝓝 p) (hae : ∀ᵐ x ∂μ, x ∈ O → x ∈ A → x ∈ B)
    (hp : p ∈ (μ.restrict A).support) : p ∈ (μ.restrict B).support := by
  obtain ⟨W,hWO,hW,hpW⟩ := mem_nhds_iff.mp hO
  rw [(nhds_basis_opens p).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  have hpos := (Measure.mem_support_iff_forall p).mp hp (U ∩ W)
    (inter_mem (hU.mem_nhds hpU) (hW.mem_nhds hpW))
  rw [Measure.restrict_apply (hU.inter hW).measurableSet] at hpos
  rw [Measure.restrict_apply hU.measurableSet]
  apply hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with x hx hxx
  exact ⟨hxx.1.1,hx (hWO hxx.1.2) hxx.2⟩

lemma measureSupport_preimage_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {D : Set Y} {p : X}
    (hq : Measure.QuasiMeasurePreserving f μ ν) (hf : ContinuousAt f p)
    (hp : p ∈ (μ.restrict (f ⁻¹' D)).support) : f p ∈ (ν.restrict D).support := by
  rw [(nhds_basis_opens (f p)).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  rw [Measure.restrict_apply hU.measurableSet]
  by_contra h
  have hzero : ν (U ∩ D) = 0 := (not_lt.mp h).antisymm bot_le
  have hz := hq.preimage_null hzero
  have hpos := (Measure.mem_support_iff_forall p).mp hp (f ⁻¹' U)
    (hf (hU.mem_nhds hpU))
  rw [Measure.restrict_apply (hU.measurableSet.preimage hq.measurable)] at hpos
  exact (ne_of_gt hpos) hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarNormalRotation_axis {n : Plane} (hn : ‖n‖ = 1) :
    planarNormalRotation n (EuclideanSpace.single 0 1) = n := by
  apply Submodule.reflection_sub
  simpa using hn.symm

lemma planarNormalRotation_radial {n : Plane} (hn : ‖n‖ = 1) (p : Plane) :
    (planarWedgeCoordinates ((planarNormalRotation n).symm p)).1 = ⟪n,p⟫ := by
  change (planeProductCoordinates ((planarNormalRotation n).symm p)).1 = _
  rw [planeProductCoordinates_apply]
  conv_rhs => lhs; rw [← planarNormalRotation_axis hn]
  conv_rhs => rhs; rw [← (planarNormalRotation n).apply_symm_apply p]
  rw [(planarNormalRotation n).inner_map_map]
  simp [EuclideanSpace.inner_single_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_punctured_ball_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball (0 : Plane) r \ {0}) := by
  let f := OpenPartialHomeomorph.univBall (0 : Plane) r
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : Plane)).isPreconnected
  have hi : f '' ({0}ᶜ : Set Plane) = Metric.ball (0 : Plane) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target (0 : Plane) hr]
        exact f.map_source (by simp [f])
      · intro he
        have he0 : f x = 0 := he
        have hh := congrArg f.symm he0
        rw [f.left_inv (by simp [f]),OpenPartialHomeomorph.univBall_symm_apply_center] at hh
        exact hx hh
    · rintro ⟨hy,hy0⟩
      have hyt : y ∈ f.target := by rwa [OpenPartialHomeomorph.univBall_target _ hr]
      refine ⟨f.symm y,?_,f.right_inv hyt⟩
      intro hz
      have hz' : f.symm y = 0 := hz
      have hh := congrArg f hz'
      rw [f.right_inv hyt,OpenPartialHomeomorph.univBall_apply_zero] at hh
      exact hy0 hh
  rw [← hi]
  exact hc.image f (OpenPartialHomeomorph.continuous_univBall (0 : Plane) r).continuousOn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_planar_perpendicular {p : Plane} (hp : p ≠ 0) :
    ∃ n : Plane, n ≠ 0 ∧ ⟪n,p⟫ = 0 := by
  let n : Plane := EuclideanSpace.single 0 (-p 1) + EuclideanSpace.single 1 (p 0)
  refine ⟨n,?_,?_⟩
  · intro hn
    have h0 := congrArg (fun y : Plane ↦ y 0) hn
    have h1 := congrArg (fun y : Plane ↦ y 1) hn
    simp [n] at h0 h1
    apply hp
    ext i
    fin_cases i <;> simp_all
  · dsimp [n]
    rw [inner_add_left,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left]
    simp only [starRingEnd_apply,star_trivial]
    ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_CoverEssentialBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma rescaled_lipschitz_graph {g : Plane → ℝ} (hg : LipschitzWith (1/4) g)
    {q : ℝ} (hq : 0 < q) : LipschitzWith (1/4) (fun y ↦ q⁻¹*g (q • y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hg.dist_le_mul (q • x) (q • y)
  rw [dist_smul₀,Real.norm_of_nonneg hq.le,Real.dist_eq] at hh
  rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hq)]
  have hi := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hq).le
  norm_num at hi ⊢
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | field_simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphMollifier_radius_tendsto :
    Tendsto (fun i ↦ (graphMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifier,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma graphSmooth_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    Tendsto (fun i ↦ graphSmooth (graphMollifier i) g y) atTop (𝓝 (g y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [mul_zero] using graphMollifier_radius_tendsto.const_mul (K:ℝ))
  exact graphSmooth_error _ hg y

theorem graphSmooth_fderiv_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ fderiv ℝ (graphSmooth (graphMollifier i) g) y)
      atTop (𝓝 (fderiv ℝ g y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi
  have ha := lipschitz_probability_average_hasFDerivAt (graphSmoothingMeasure_ac (graphMollifier i))
    hg (graphMollifier i).rOut_pos.le (graphSmoothingMeasure_radius (graphMollifier i)) y
  change dist (fderiv ℝ (fun z ↦ ∫ w, g (z-w) ∂graphSmoothingMeasure (graphMollifier i)) y) _ < ε
  rw [ha.2.fderiv,dist_eq_norm]
  have he : (∫ _w : Plane, fderiv ℝ g y ∂graphSmoothingMeasure (graphMollifier i)) = fderiv ℝ g y := by simp
  rw [← he,← integral_sub ha.1 (integrable_const _)]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have hb : (∫ w, ‖fderiv ℝ g (y-w)-fderiv ℝ g y‖ ∂graphSmoothingMeasure (graphMollifier i)) ≤ ε/2 := by
    calc
      _ ≤ ∫ _w : Plane, ε/2 ∂graphSmoothingMeasure (graphMollifier i) := by
        apply integral_mono_ae (ha.1.sub (integrable_const _)).norm (integrable_const _)
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with w hw
        have hh : dist (y-w) y < δ := by simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hw.trans_lt hi
        simpa only [dist_eq_norm,Pi.sub_apply] using (hclose hh).le
      _ = _ := by simp
  exact hb.trans_lt (by linarith)

lemma graphSmooth_gradient_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ gradient (graphSmooth (graphMollifier i) g) y) atTop (𝓝 (gradient g y)) := by
  exact ((InnerProductSpace.toDual ℝ Plane).symm.continuous.tendsto _).comp
    (graphSmooth_fderiv_tendsto hg hc)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_trace_volume_zero (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) :
    volume {x : Cover | ⟪n,x-a⟫ = graphHeightExtension a n g x} = 0 := by
  have hz : volume {x : Cover | ⟪n,x-a⟫ = 0} = 0 := by
    simpa only [Set.preimage_ofPred_eq,sub_eq_add_neg] using
      (measurePreserving_add_right volume (-a)).quasiMeasurePreserving.preimage_null
        (hyperplane_volume_zero hn)
  have hh := (graphShear_measurePreserving a hn hg.neg.measurable).quasiMeasurePreserving.preimage_null hz
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,graphShear,normalMove,graphHeightExtension,
    add_sub_right_comm,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,
    one_pow,mul_one,Pi.neg_apply]
  constructor <;> intro h <;> linarith

lemma measurable_graphSublevelIndicator (a n : Cover) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (graphSublevelIndicator a n g) := by
  exact measurable_const.indicator (measurableSet_lt (by fun_prop)
    (hg.comp ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const))))

lemma graphSublevelIndicator_bound (a n : Cover) (g : Plane → ℝ) (x : Cover) :
    |graphSublevelIndicator a n g x| ≤ 1 := by
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

lemma graphSublevelIndicator_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (a n : Cover) {x : Cover} (hx : ⟪n,x-a⟫ ≠ graphHeightExtension a n g x) :
    Tendsto (fun i ↦ graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphSublevelIndicator a n g x)) := by
  have ht := graphSmooth_tendsto hg (normalPlaneCoordinates n (x-a))
  have he : ∀ᶠ i in atTop,
      graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x = graphSublevelIndicator a n g x := by
    by_cases hl : ⟪n,x-a⟫ < graphHeightExtension a n g x
    · filter_upwards [ht.eventually (Ioi_mem_nhds hl)] with i hi
      change (if ⟪n,x-a⟫ < graphSmooth (graphMollifier i) g (normalPlaneCoordinates n (x-a)) then (1:ℝ) else 0) = _
      rw [ite_eq_left hi]
      exact (indicator_of_mem hl (fun _ ↦ (1:ℝ))).symm
    · have hh : graphHeightExtension a n g x < ⟪n,x-a⟫ := lt_of_le_of_ne (not_lt.mp hl) hx.symm
      filter_upwards [ht.eventually (Iio_mem_nhds hh)] with i hi
      have hi' : ¬ ⟪n,x-a⟫ < graphHeightExtension a n (graphSmooth (graphMollifier i) g) x := not_lt.mpr hi.le
      simp [graphSublevelIndicator,hl,hi']
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with i hi
  exact hi.symm

lemma graphSublevel_flux_mollification_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    Tendsto (fun i ↦ ∫ x : Cover, graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x * divergence F x)
      atTop (𝓝 (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x)) := by
  have hi : Integrable (divergence F) := (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖divergence F x‖)
    (fun i ↦ ((measurable_graphSublevelIndicator a n (graphSmooth_contDiff _ hg).continuous.measurable).mul
      (continuous_divergence hF).measurable).aestronglyMeasurable) hi.norm
  · intro i
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (graphSublevelIndicator_bound a n _ x)
  · have hae : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
      simpa only [ae_iff,not_not] using graph_trace_volume_zero a hn hg.continuous
    filter_upwards [hae] with x hx
    exact (graphSublevelIndicator_tendsto hg a n hx).mul_const _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_norm_linear {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphAreaVector n g y‖ ≤ 1+(K:ℝ) := by
  calc
    _ ≤ ‖n‖+‖normalPlaneEmbedding n (gradient g y)‖ := norm_sub_le _ _
    _ = 1+‖fderiv ℝ g y‖ := by rw [hn,normalPlaneEmbedding_norm,plane_gradient_norm]
    _ ≤ _ := add_le_add le_rfl (norm_fderiv_le_of_lipschitz ℝ hg)

lemma graph_trace_zero_outside {X : Type*} [Zero X] {a n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → X} {R : ℝ} (hs : tsupport F ⊆ Metric.closedBall a R)
    (g : Plane → ℝ) {y : Plane} (hy : y ∉ Metric.closedBall (0 : Plane) R) :
    F (a+normalGraph n g y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] at hh
  exact hy (by simpa only [Metric.mem_closedBall,dist_zero_right] using
    (normalGraph_norm_ge hn g y).trans hh)

theorem integral_C1graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hFs : HasCompactSupport F := (isCompact_closedBall a R).of_isClosed_subset isClosed_closure hs
  obtain ⟨M,hM⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hFs.norm
  have hMb (x : Cover) : ‖F x‖ ≤ M := hM (mem_range_self x)
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hMb 0)
  let B : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator (fun _ ↦ (1+(K:ℝ))*M)
  have hBi : Integrable B := (integrableOn_const (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have ht : Tendsto (fun i ↦ ∫ y : Plane,
      ⟪graphAreaVector n (graphSmooth (graphMollifier i) g) y,
        F (a+normalGraph n (graphSmooth (graphMollifier i) g) y)⟫) atTop
      (𝓝 (∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun i ↦ ((graphAreaVector_continuous n (graphSmooth_contDiff _ hg)).inner
        (graph_trace_continuous a n (graphSmooth_contDiff _ hg).continuous hF.continuous)).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · rw [show B y = (1+(K:ℝ))*M from indicator_of_mem hy _]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (graphAreaVector_norm_linear hn (graphSmooth_lipschitz _ hg) y)
            (hMb _) (norm_nonneg _) (by positivity))
      · rw [graph_trace_zero_outside hn hs _ hy,inner_zero_right,norm_zero,
          show B y = 0 from indicator_of_notMem hy _]
    · filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · have hd := graphSmooth_gradient_tendsto hg (hc y hy)
        have hnG : Tendsto (fun i ↦ normalGraph n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (normalGraph n g y)) :=
          tendsto_const_nhds.add ((graphSmooth_tendsto hg y).smul_const n)
        have hnA : Tendsto (fun i ↦ graphAreaVector n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (graphAreaVector n g y)) :=
          tendsto_const_nhds.sub (((normalPlaneLinearIsometry n).continuous.tendsto _).comp hd)
        exact hnA.inner ((hF.continuous.tendsto _).comp (tendsto_const_nhds.add hnG))
      · simp only [graph_trace_zero_outside hn hs _ hy,inner_zero_right]
        exact tendsto_const_nhds
  apply tendsto_nhds_unique (graphSublevel_flux_mollification_tendsto a hn hg hF hFs)
  simpa only [integral_graphSublevel_divergence a hn (graphSmooth_contDiff _ hg) hF hFs] using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_continuousAt (n : Cover) {g : Plane → ℝ} {y : Plane}
    (hc : ContinuousAt (fderiv ℝ g) y) : ContinuousAt (graphAreaVector n g) y := by
  exact continuousAt_const.sub ((normalPlaneLinearIsometry n).continuous.continuousAt.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hc))

lemma graph_weighted_continuous (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Continuous (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
  · exact (graph_trace_continuous a n hg hφ).continuousAt.mul (hψ y hy)
  · have he : (fun z : Plane ↦ φ (a+normalGraph n g z)*ψ z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [graph_trace_zero_outside hn hs _ hz,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma graph_weighted_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Integrable (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) :=
  (graph_weighted_continuous a hn hg hφ hs hψ).integrable_of_hasCompactSupport
    (graph_trace_compactSupport a hn hg hsφ).mul_right

lemma setIntegral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x in {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x}, divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  rw [← integral_C1graphSublevel_divergence a hn hg hc hF hs]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  rw [← integral_indicator hm]
  congr 1
  funext x
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

theorem blowup_graph_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA hm hgraph
      ((tsupport_smul_subset_left _ _).trans hφU),
    setIntegral_graphSublevel_divergence a hn hg hc hH
      ((tsupport_smul_subset_left _ _).trans hφR)] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_contDiff (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphUnitNormalExtension a n g) := by
  have hd := hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp hd
  exact (graphSlopeNormal_contDiff hn).comp (hgrad.comp
    ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma graphUnitNormalExtension_graph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g f : Plane → ℝ) (y : Plane) :
    graphUnitNormalExtension a n f (a+normalGraph n g y) = graphSlopeNormal n (gradient f y) := by
  unfold graphUnitNormalExtension
  rw [add_sub_cancel_left,normalGraph, map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]

lemma graphUnitNormalExtension_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {x : Cover}
    (hc : ContinuousAt (fderiv ℝ g) (normalPlaneCoordinates n (x-a))) :
    Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphUnitNormalExtension a n g x)) :=
  ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp (graphSmooth_gradient_tendsto hg hc)

lemma graphAreaVector_inner_unit {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪graphAreaVector n g y,graphSlopeNormal n (gradient g y)⟫ = ‖graphAreaVector n g y‖ := by
  have hh : 0 < ‖graphAreaVector n g y‖ := lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn _)
  rw [graphSlopeNormal,inner_smul_right,show n-normalPlaneEmbedding n (gradient g y)=graphAreaVector n g y from rfl,
    real_inner_self_eq_norm_sq]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_area_trace_mollified_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφ0 : ∀ x, 0 ≤ φ x) :
    Tendsto (fun i ↦ ∫ y : Plane, φ (a+normalGraph n g y)*
      ⟪graphAreaVector n g y,graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) (a+normalGraph n g y)⟫)
      atTop (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
  have hi := graph_weighted_integrable a hn hg.continuous hφ hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  apply tendsto_integral_of_dominated_convergence
    (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) ?_ hi
  · intro i
    filter_upwards [] with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    exact (norm_inner_le_norm _ _).trans_eq (by rw [graphUnitNormalExtension_unit a hn,mul_one])
  · filter_upwards [] with y
    by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
    · have ht : Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
          (a+normalGraph n g y)) atTop (𝓝 (graphSlopeNormal n (gradient g y))) := by
        simp only [graphUnitNormalExtension_graph a hn]
        exact ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp
          (graphSmooth_gradient_tendsto hg (hc y hy))
      simpa only [graphAreaVector_inner_unit hn] using ((show Tendsto (fun _ : ℕ ↦ graphAreaVector n g y) atTop
        (𝓝 (graphAreaVector n g y)) from tendsto_const_nhds).inner ht).const_mul (φ (a+normalGraph n g y))
    · simp only [graph_trace_zero_outside hn hφR _ hy,zero_mul]
      exact tendsto_const_nhds
  · intro i
    exact (graph_weighted_continuous a hn hg.continuous hφ hφR (fun y hy ↦
      (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous
          (graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)).continuous).continuousAt)).aestronglyMeasurable

theorem blowup_graph_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiArea := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hiF (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound hnF z)
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤
        ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
      (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous hF.continuous).continuousAt)) hiArea
    intro y
    apply mul_le_mul_of_nonneg_left _ (hφb _).1
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnF _))
  refine le_antisymm ?_ ?_
  · exact blowupNormal_weighted_saturation heq hflux hiφ (by norm_num : (0 : ℝ)<1)
      (fun z ↦ (hφb z.1).2) (fun F hF _ _ hnF ↦ hfield F hF hnF)
  · apply le_of_tendsto (graph_area_trace_mollified_normal_tendsto a hn hg hc
      hφ.continuous hsφ hφR (fun x ↦ (hφb x).1))
    apply Eventually.of_forall
    intro i
    let F := graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
    have hnF (x : Cover) : ‖F x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
    rw [← blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (hiF F hF hnF) hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) (F z.1)).trans (by rw [z.2.property,one_mul]; exact hnF _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_norm_le (n x : Cover) : ‖normalPlaneCoordinates n x‖ ≤ ‖x‖ := by
  simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using
    (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0

lemma graph_weighted_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφR : tsupport φ ⊆ Metric.closedBall a R) (z : BlowupNormalBundle) :
    Tendsto (fun i ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n
      (graphSmooth (graphMollifier i) g) z.1⟫) atTop
      (𝓝 (φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)) := by
  by_cases hz : z.1 ∈ tsupport φ
  · have hcoord : normalPlaneCoordinates n (z.1-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hz)
    exact ((show Tendsto (fun _ : ℕ ↦ (z.2 : Cover)) atTop (𝓝 (z.2 : Cover)) from
      tendsto_const_nhds).inner (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hz,zero_mul]
    exact tendsto_const_nhds

theorem blowup_graph_patch_normal_ae {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let F : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let f : ℕ → BlowupNormalBundle → ℝ := fun i z ↦ φ z.1*⟪(z.2 : Cover),F i z.1⟫
  let f₀ : BlowupNormalBundle → ℝ := fun z ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hFn (i) (x) : ‖F i x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
  have hf (i) : AEStronglyMeasurable (f i) μ :=
    (show Continuous (f i) from (hφ.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd |>.inner ((hF i).continuous.comp continuous_fst))).aestronglyMeasurable
  have ht : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 (f₀ z)) :=
    ae_of_all μ (graph_weighted_normal_tendsto a hn hg hc hφR)
  have hb (i) (z : BlowupNormalBundle) : ‖f i z‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound (hFn i) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb₀ (z : BlowupNormalBundle) : ‖f₀ z‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound
      (fun x ↦ (graphUnitNormalExtension_unit a hn _ x).le) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hi₀ : Integrable f₀ μ := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hf ht) 1 (ae_of_all μ hb₀)
  have hilim : Tendsto (fun i ↦ ∫ z, f i z ∂μ) atTop (𝓝 (∫ z, f₀ z ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hf
      (integrable_const 1) (fun i ↦ ae_of_all μ (hb i)) ht
  have heint : (∫ z, f₀ z ∂μ) = ∫ z, φ z.1 ∂μ := by
    apply tendsto_nhds_unique hilim
    rw [show (∫ z, φ z.1 ∂μ) = _ from
      blowup_graph_patch_weighted_mass hA a hn hg hc hgraph heq hflux hφ hsφ hφU hφO hφR hφb]
    have hh := graph_area_trace_mollified_normal_tendsto a hn hg hc hφ.continuous hsφ hφR
      (fun x ↦ (hφb x).1)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb (hF i) (hFn i)
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hinon (z : BlowupNormalBundle) : 0 ≤ φ z.1-f₀ z := by
    have hh : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ ≤ 1 := by
      exact (real_inner_le_norm _ _).trans_eq (by rw [z.2.property,graphUnitNormalExtension_unit a hn,one_mul])
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hφb _).1 hh)
  have hezero : (∫ z, (φ z.1-f₀ z) ∂μ)=0 := by rw [integral_sub hiφ hi₀,heint,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hinon) (hiφ.sub hi₀)).mp hezero
  filter_upwards [hae] with z hz
  intro hzφ
  have hi : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ = 1 := by
    have hh : φ z.1*(1-⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)=0 := by
      simpa only [mul_sub,mul_one,f₀,Pi.zero_apply] using hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hzφ.ne')).symm
  exact (inner_eq_one_iff_of_norm_eq_one z.2.property (graphUnitNormalExtension_unit a hn g z.1)).mp hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem blowup_graph_patch_signed_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfb : ∀ x, |f x| ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let ψ : Cover → ℝ := fun x ↦ φ x*((1+f x)/2)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul ((contDiff_const.add hf).div_const 2)
  have hsψ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_left
  have hψb (x : Cover) : ψ x ∈ Icc 0 1 := by
    have hx := abs_le.mp (hfb x)
    have hhalf : (1+f x)/2 ∈ Icc 0 1 := ⟨by linarith,by linarith⟩
    exact ⟨mul_nonneg (hφb x).1 hhalf.1,
      (mul_le_mul (hφb x).2 hhalf.2 hhalf.1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsψ' : HasCompactSupport ψ := hsφ.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hmψ := blowup_graph_patch_weighted_mass hA a hn hg hc hgraph heq hflux hψ hsψ'
    (hsψ.trans hφU) (hsψ.trans hφO) (hsψ.trans hφR) hψb
  have hmφ := blowup_graph_patch_weighted_mass hA a hn hg hc hgraph heq hflux hφ hsφ hφU hφO hφR hφb
  have hI (w : Cover → ℝ) (hw : Continuous w) (hb : ∀ x, w x ∈ Icc 0 1) :
      Integrable (fun z : BlowupNormalBundle ↦ w z.1) μ :=
    Integrable.of_bound (hw.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb _).1]; exact (hb _).2)
  have hGφ := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hGψ := graph_weighted_integrable a hn hg.continuous hψ.continuous hsψ' (hsψ.trans hφR)
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  calc
    (∫ z, φ z.1*f z.1 ∂μ) = ∫ z, (2*ψ z.1-φ z.1) ∂μ := by
      congr 1; funext z; dsimp only [ψ]; ring
    _ = 2*(∫ z, ψ z.1 ∂μ)-(∫ z, φ z.1 ∂μ) := by
      rw [integral_sub ((hI ψ hψ.continuous hψb).const_mul 2) (hI φ hφ.continuous hφb),integral_const_mul]
    _ = 2*(∫ y : Plane, ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by rw [hmψ,hmφ]
    _ = ∫ y : Plane, (2*(ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by
      rw [integral_sub (hGψ.const_mul 2) hGφ,integral_const_mul]
    _ = _ := by congr 1; funext y; dsimp only [ψ]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weighted_tendsto_on_tsupport {X : Type*} [TopologicalSpace X]
    {φ : X → ℝ} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : ∀ x ∈ tsupport φ, Tendsto (fun i ↦ f i x) atTop (𝓝 (g x))) (x : X) :
    Tendsto (fun i ↦ φ x*f i x) atTop (𝓝 (φ x*g x)) := by
  by_cases hx : x ∈ tsupport φ
  · exact (h x hx).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    exact tendsto_const_nhds

theorem blowup_graph_patch_limit_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {f : ℕ → Cover → ℝ} {f₀ : Cover → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (hfb : ∀ i x, |f i x| ≤ 1)
    (hlim : ∀ x ∈ tsupport φ, Tendsto (fun i ↦ f i x) atTop (𝓝 (f₀ x))) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f₀ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hleft : Tendsto (fun i ↦ ∫ z, φ z.1*f i z.1 ∂μ) atTop (𝓝 (∫ z, φ z.1*f₀ z.1 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ))
    · intro i
      exact ((hφ.continuous.mul (hf i).continuous).comp continuous_fst).aestronglyMeasurable
    · exact integrable_const 1
    · intro i
      filter_upwards [] with z
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs]
      exact (mul_le_mul (hφb _).2 (hfb i _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · exact ae_of_all μ fun z ↦ weighted_tendsto_on_tsupport hlim z.1
  have hright : Tendsto (fun i ↦ ∫ y : Plane,
      φ (a+normalGraph n g y)*f i (a+normalGraph n g y)*‖graphAreaVector n g y‖) atTop
      (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)
    · intro i
      have hh := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
      have hmeas : AEStronglyMeasurable (fun y : Plane ↦
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)*f i (a+normalGraph n g y))
          (volume : Measure Plane) :=
        (hh.mul (graph_trace_continuous a n hg.continuous (hf i).continuous)).aestronglyMeasurable
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hmeas
    · exact graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
    · intro i
      filter_upwards [] with y
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs,
        norm_norm]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hφb _).1 (hfb i _)) (norm_nonneg _)
    · filter_upwards [] with y
      exact (weighted_tendsto_on_tsupport hlim _).mul_const _
  apply tendsto_nhds_unique hleft
  convert hright using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact blowup_graph_patch_signed_mass hA a hn hg hc hgraph heq hflux hφ hsφ hφU hφO hφR hφb (hf i) (hfb i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma contDiff_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  have hd := hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  unfold divergence
  apply ContDiff.sum
  intro i _
  exact (EuclideanSpace.proj i).contDiff.comp (hd.clm_apply contDiff_const)

lemma contDiff_tangentialDivergence_normal {F N : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ tangentialDivergence F x (N x)) :=
  (contDiff_divergence hF).sub (hN.inner ℝ ((hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply hN))

lemma continuous_tangentialDivergence_normal (F : Cover → Cover) (x : Cover) :
    Continuous (fun v : Cover ↦ tangentialDivergence F x v) :=
  continuous_const.sub (continuous_id.inner ((fderiv ℝ F x).continuous.comp continuous_id))

theorem blowup_C1graph_stationary {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsF : HasCompactSupport F)
    (hφF : ∀ x ∈ tsupport F, φ x = 1)
    (hstat : (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0) :
    (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let M : ℝ := ‖blowupTangentTest hF hsF‖+1
  have hM : 0 < M := by dsimp only [M]; positivity
  let N : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let N₀ := graphUnitNormalExtension a n g
  let f : ℕ → Cover → ℝ := fun i x ↦ M⁻¹*tangentialDivergence F x (N i x)
  let f₀ : Cover → ℝ := fun x ↦ M⁻¹*tangentialDivergence F x (N₀ x)
  have hN (i) : ContDiff ℝ (⊤ : ℕ∞) (N i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hf (i) : ContDiff ℝ (⊤ : ℕ∞) (f i) :=
    contDiff_const.mul (contDiff_tangentialDivergence_normal hF (hN i))
  have hfb (i) (x) : |f i x| ≤ 1 := by
    have hh := (blowupTangentTest hF hsF).norm_coe_le_norm
      (x,⟨N i x,graphUnitNormalExtension_unit a hn _ x⟩)
    change ‖tangentialDivergence F x (N i x)‖ ≤ ‖blowupTangentTest hF hsF‖ at hh
    dsimp only [f]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hM)]
    apply (mul_le_mul_of_nonneg_left (hh.trans (le_add_of_nonneg_right zero_le_one)) (inv_nonneg.mpr hM.le)).trans_eq
    exact inv_mul_cancel₀ hM.ne'
  have hlim (x : Cover) (hx : x ∈ tsupport φ) : Tendsto (fun i ↦ f i x) atTop (𝓝 (f₀ x)) := by
    have hcoord : normalPlaneCoordinates n (x-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hx)
    exact (((continuous_tangentialDivergence_normal F x).tendsto _).comp
      (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul M⁻¹
  have he := blowup_graph_patch_limit_mass hA a hn hg hc hgraph heq hflux hφ hsφ hφU hφO hφR hφb hf hfb hlim
  have hae := blowup_graph_patch_normal_ae hA a hn hg hc hgraph heq hflux hφ hsφ hφU hφO hφR hφb
  have hw (x v) : φ x*tangentialDivergence F x v=tangentialDivergence F x v := by
    by_cases hx : x ∈ tsupport F
    · rw [hφF x hx,one_mul]
    · rw [tangentialDivergence_zero_of_notMem_tsupport hx,mul_zero]
  have hFO : tsupport F ⊆ O := by
    intro x hx
    apply hφO
    exact subset_tsupport _ (by rw [Function.mem_support,hφF x hx]; exact one_ne_zero)
  have hleft : (∫ z, φ z.1*f₀ z.1 ∂μ)=0 := by
    calc
      (∫ z, φ z.1*f₀ z.1 ∂μ) = ∫ z, M⁻¹*tangentialDivergence F z.1 z.2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hae] with z hz
        by_cases hzφ : 0 < φ z.1
        · dsimp only [f₀,N₀]
          rw [← hz hzφ,← mul_assoc,mul_comm (φ z.1) M⁻¹,mul_assoc,hw]
        · have hφz : φ z.1=0 := le_antisymm (le_of_not_gt hzφ) (hφb _).1
          dsimp only [f₀]
          rw [hφz,zero_mul,← hw z.1 (z.2 : Cover),hφz,zero_mul,mul_zero]
      _ = M⁻¹*(∫ z, tangentialDivergence F z.1 z.2 ∂μ) := integral_const_mul _ _
      _ = M⁻¹*(∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) := by
        congr 1
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        exact tangentialDivergence_zero_of_notMem_tsupport (fun h ↦ hz (hFO h)) _
      _ = 0 := by rw [hstat,mul_zero]
  have hright : (∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖) =
      M⁻¹*(∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    dsimp only [f₀,N₀]
    rw [graphUnitNormalExtension_graph a hn,← mul_assoc (φ _) M⁻¹,mul_comm (φ _) M⁻¹,mul_assoc M⁻¹,hw]
    ring
  rw [hright,hleft] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (inv_ne_zero hM.ne')

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalCoverMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverEssentialBoundary_eq_support (A : Set Cover) :
    coverEssentialBoundary A = (volume.restrict A).support ∩ (volume.restrict Aᶜ).support := by
  ext p
  simp only [coverEssentialBoundary,Set.mem_ofPred_eq,Set.mem_inter_iff,
    Metric.nhds_basis_ball.mem_measureSupport,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet,inter_comm,forall_and]
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨fun r hr ↦ (ENNReal.toReal_pos_iff).mp (ha r hr) |>.1,
      fun r hr ↦ (ENNReal.toReal_pos_iff).mp (hc r hr) |>.1⟩
  · rintro ⟨ha,hc⟩
    refine ⟨fun r hr ↦ ?_,fun r hr ↦ ?_⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨ha r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨hc r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩

lemma cover_boundary_local_ae {A B U : Set Cover} {p : Cover}
    (hU : U ∈ 𝓝 p) (hae : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ B))
    (hp : p ∈ coverEssentialBoundary A) : p ∈ coverEssentialBoundary B := by
  rw [coverEssentialBoundary_eq_support] at hp ⊢
  exact ⟨measureSupport_local_ae_mono hU (hae.mono (fun _ h hu ↦ (h hu).mp)) hp.1,
    measureSupport_local_ae_mono hU (hae.mono (fun _ h hu ↦ (not_congr (h hu)).mp)) hp.2⟩

lemma cover_boundary_preimage_image {A : Set Cover} {f : Cover → Cover} {p : Cover}
    (hq : Measure.QuasiMeasurePreserving f volume volume) (hf : ContinuousAt f p)
    (hp : p ∈ coverEssentialBoundary (f ⁻¹' A)) : f p ∈ coverEssentialBoundary A := by
  rw [coverEssentialBoundary_eq_support] at hp ⊢
  exact ⟨measureSupport_preimage_image hq hf hp.1,measureSupport_preimage_image hq hf hp.2⟩

lemma cover_boundary_measurePreserving_homeomorph {A : Set Cover} (f : Cover ≃ₜ Cover)
    (hq : MeasurePreserving f) (p : Cover) :
    p ∈ coverEssentialBoundary (f ⁻¹' A) ↔ f p ∈ coverEssentialBoundary A := by
  constructor
  · exact cover_boundary_preimage_image hq.quasiMeasurePreserving f.continuous.continuousAt
  · intro hp
    have hi : MeasurePreserving f.symm := MeasurePreserving.symm f.toMeasurableEquiv hq
    have hh := cover_boundary_preimage_image hi.quasiMeasurePreserving f.symm.continuous.continuousAt
      (A := f ⁻¹' A) (p := f p)
    have he : f.symm ⁻¹' (f ⁻¹' A) = A := by ext x; simp
    rw [he] at hh
    simpa only [f.symm_apply_apply] using hh hp

theorem connected_cover_phase {A s : Set Cover} (hA : MeasurableSet A)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (coverEssentialBoundary A)) :
    volume (s ∩ A) = 0 ∨ volume (s ∩ Aᶜ) = 0 := by
  rw [coverEssentialBoundary_eq_support] at hd
  let U := (volume.restrict A).supportᶜ
  let W := (volume.restrict Aᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict A).support ∪ (volume.restrict Aᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hA,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict A).supportᶜ ∩ (volume.restrict Aᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    exact not_and_or.mp (fun hb ↦ Set.disjoint_left.mp hd hx hb)
  have hnullA (h : s ⊆ U) : volume (s ∩ A) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Aᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullA (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_halfballs_null {A : Set Cover} {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) = 0)
    (hr : volume ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) = 0) :
    volume (Metric.ball (0 : Cover) r ∩ A) = 0 := by
  apply measure_mono_null (t := ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) ∪
    ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) ∪ {y | ⟪n,y⟫ = 0}) ?_
    (measure_union_null (measure_union_null hl hr) (hyperplane_volume_zero hn))
  intro y hy
  rcases lt_trichotomy ⟪n,y⟫ 0 with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨hy.1,hh⟩,hy.2⟩)
  · exact Or.inr hh
  · exact Or.inl (Or.inr ⟨⟨hy.1,hh⟩,hy.2⟩)

lemma cover_opposite_halfballs_model {C : Set Cover} {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) = 0)
    (hr : volume ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) = 0) :
    ∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  have hal : ∀ᵐ y : Cover ∂volume, ¬(y ∈ (Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hl
  have har : ∀ᵐ y : Cover ∂volume, ¬(y ∈ (Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hr
  have han : ∀ᵐ y : Cover ∂volume, ⟪n,y⟫ ≠ 0 := by
    simpa only [ae_iff,not_not] using hyperplane_volume_zero hn
  filter_upwards [hal,har,han] with y hl hr hne hy
  constructor
  · intro hc
    by_contra hpos
    exact hl ⟨⟨hy,lt_of_le_of_ne (not_lt.mp hpos) hne⟩,hc⟩
  · intro hpos
    by_contra hnc
    exact hr ⟨⟨hy,hpos⟩,hnc⟩

theorem cover_boundary_plane_phases {C : Set Cover} (hC : MeasurableSet C)
    {r : ℝ} {n : Cover} (hn : ‖n‖ = 1)
    (hbd : ∀ y : Cover, y ∈ Metric.ball (0 : Cover) r → y ∈ coverEssentialBoundary C → ⟪n,y⟫ = 0)
    (hpos : 0 < volume (Metric.ball (0 : Cover) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Cover) r ∩ Cᶜ)) :
    (∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ 0 < ⟪n,y⟫)) ∨
    (∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ ⟪n,y⟫ < 0)) := by
  let U := Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}
  let W := Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet
  have hW : MeasurableSet W := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt continuous_const (innerSL ℝ n).continuous).measurableSet
  have hcU : IsPreconnected U := ((convex_ball (0 : Cover) r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hcW : IsPreconnected W := ((convex_ball (0 : Cover) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hdU : Disjoint U (coverEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_lt hy.2) (hbd y hy.1 he)
  have hdW : Disjoint W (coverEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_gt hy.2) (hbd y hy.1 he)
  rcases connected_cover_phase hC hU hcU hdU with hu|hu <;>
    rcases connected_cover_phase hC hW hcW hdW with hw|hw
  · exact ((ne_of_gt hpos) (cover_halfballs_null hn hu hw)).elim
  · exact Or.inl (cover_opposite_halfballs_model hn hu hw)
  · apply Or.inr
    have hneg : ‖-n‖ = 1 := by simpa using hn
    have hh := cover_opposite_halfballs_model hneg
      (by simpa only [inner_neg_left,neg_lt_zero] using hw)
      (by simpa only [inner_neg_left,neg_pos] using hu)
    simpa only [inner_neg_left,neg_pos] using hh
  · exact ((ne_of_gt hneg) (cover_halfballs_null hn hu hw)).elim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cover_flattened_boundary_phases {A U : Set Cover} (hA : MeasurableSet A)
    (f : Cover ≃ₜ Cover) (hmp : MeasurePreserving f) {n : Cover} (hn : ‖n‖ = 1)
    (hU : U ∈ 𝓝 (f 0)) (hp : f 0 ∈ coverEssentialBoundary A)
    (hbd : ∀ x : Cover, f x ∈ U → f x ∈ coverEssentialBoundary A → ⟪n,x⟫ = 0) :
    ∃ W : Set Cover, IsOpen W ∧ f 0 ∈ W ∧ W ⊆ U ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ 0 < ⟪n,f.symm x⟫)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ ⟪n,f.symm x⟫ < 0))) := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (f.continuous.continuousAt.preimage_mem_nhds hU)
  let C := f ⁻¹' A
  have hC : MeasurableSet C := hA.preimage f.continuous.measurable
  have h0 : (0 : Cover) ∈ coverEssentialBoundary C := (cover_boundary_measurePreserving_homeomorph f hmp 0).mpr hp
  have hh := h0 r hr
  have hpos : 0 < volume (Metric.ball (0 : Cover) r ∩ C) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hh.1).1
  have hneg : 0 < volume (Metric.ball (0 : Cover) r ∩ Cᶜ) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hh.2).1
  have hplanes : ∀ x : Cover, x ∈ Metric.ball (0 : Cover) r → x ∈ coverEssentialBoundary C → ⟪n,x⟫=0 :=
    fun x hx hb ↦ hbd x (hsub hx) ((cover_boundary_measurePreserving_homeomorph f hmp x).mp hb)
  have hinv := (MeasurePreserving.symm f.toMeasurableEquiv hmp).quasiMeasurePreserving
  refine ⟨f '' Metric.ball (0 : Cover) r, f.isOpenMap _ Metric.isOpen_ball,
    ⟨0,by simpa using hr,rfl⟩,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact hsub hy
  · rcases cover_boundary_plane_phases hC hn hplanes hpos hneg with h|h
    · left
      filter_upwards [hinv.ae h] with x hx
      intro hW
      obtain ⟨y,hy,rfl⟩ := hW
      change f.symm (f y) ∈ Metric.ball (0 : Cover) r → (f.symm (f y) ∈ C ↔ 0 < ⟪n,f.symm (f y)⟫) at hx
      have hh := hx (by simpa using hy)
      change (f.symm (f y) ∈ C ↔ _) at hh
      simpa only [f.symm_apply_apply,C,Set.mem_preimage] using hh
    · right
      filter_upwards [hinv.ae h] with x hx
      intro hW
      obtain ⟨y,hy,rfl⟩ := hW
      change f.symm (f y) ∈ Metric.ball (0 : Cover) r → (f.symm (f y) ∈ C ↔ ⟪n,f.symm (f y)⟫ < 0) at hx
      have hh := hx (by simpa using hy)
      change (f.symm (f y) ∈ C ↔ _) at hh
      simpa only [f.symm_apply_apply,C,Set.mem_preimage] using hh

lemma graphSignedHeight_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSignedHeight a n g (graphShear a n g x) = ⟪n,x-a⟫ := by
  unfold graphSignedHeight graphHeightExtension
  rw [graphShear_projection a hn]
  simp only [graphShear,normalMove,graphHeightExtension,add_sub_right_comm,
    inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  ring

lemma graphSignedHeight_graph {a n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    {x : Cover} (hx : normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    graphSignedHeight a n g x = 0 := by
  have hh := congrArg (fun z : Cover ↦ ⟪n,z⟫) hx
  rw [normalGraph_inner hn] at hh
  exact sub_eq_zero.mpr hh.symm

theorem cover_graph_boundary_phases {A U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {p : Cover} (hU : U ∈ 𝓝 p) (hp : p ∈ coverEssentialBoundary A)
    (hbd : ∀ x ∈ U, x ∈ coverEssentialBoundary A →
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    ∃ W : Set Cover, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ 0 < graphSignedHeight a n g x)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ graphSignedHeight a n g x < 0))) := by
  let h := graphShearHomeomorph a hn hg
  let q := h.symm p
  let f := (Homeomorph.addLeft q).trans h
  have hf0 : f 0 = p := by simp [f,q]
  have hmp : MeasurePreserving f :=
    (graphShear_measurePreserving a hn hg.measurable).comp (measurePreserving_add_left volume q)
  have hq : ⟪n,q-a⟫ = 0 := by
    have hh := graphSignedHeight_graph hn g (hbd p (mem_of_mem_nhds hU) hp)
    have he := graphSignedHeight_shear a hn g q
    change graphSignedHeight a n g (h q) = _ at he
    rw [show h q = p from h.apply_symm_apply p] at he
    exact he.symm.trans hh
  have he (x : Cover) : graphSignedHeight a n g (f x) = ⟪n,x⟫ := by
    change graphSignedHeight a n g (graphShear a n g (q+x)) = _
    rw [graphSignedHeight_shear a hn,add_sub_right_comm,inner_add_right,hq,zero_add]
  have hbd' (x : Cover) (hx : f x ∈ U) (hb : f x ∈ coverEssentialBoundary A) : ⟪n,x⟫=0 := by
    rw [← he]
    exact graphSignedHeight_graph hn g (hbd _ hx hb)
  obtain ⟨W,hW,hpW,hWU,hph⟩ := cover_flattened_boundary_phases hA f hmp hn
    (by simpa only [hf0] using hU) (by simpa only [hf0] using hp) hbd'
  refine ⟨W,hW,by simpa only [hf0] using hpW,hWU,?_⟩
  have hei (x : Cover) : ⟪n,f.symm x⟫ = graphSignedHeight a n g x := by
    rw [← he,f.apply_symm_apply]
  simpa only [hei] using hph

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_dilated (n : Cover) (g : Plane → ℝ) {s : ℝ} (hs : s ≠ 0) (y : Plane) :
    normalGraph n (dilatedGraph s g) y = s • normalGraph n g (s⁻¹ • y) := by
  unfold normalGraph dilatedGraph
  simp only [smul_add,smul_smul]
  change normalPlaneLinearIsometry n y+_ = s • normalPlaneLinearIsometry n (s⁻¹ • y)+_
  rw [map_smul,smul_smul,mul_inv_cancel₀ hs,one_smul]

lemma dilatedGraph_lipschitz {g : Plane → ℝ} (hg : LipschitzWith (1/4) g)
    {s : ℝ} (hs : 0 < s) : LipschitzWith (1/4) (dilatedGraph s g) := by
  change LipschitzWith (1/4) (fun y : Plane ↦ s*g (s⁻¹ • y))
  convert rescaled_lipschitz_graph hg (inv_pos.mpr hs) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [inv_inv]

lemma dilatedGraph_contDiffAt {g : Plane → ℝ} {s : ℝ} {y : Plane}
    (hg : ContDiffAt ℝ 1 g (s⁻¹ • y)) : ContDiffAt ℝ 1 (dilatedGraph s g) y :=
  contDiffAt_const.mul (hg.comp y (contDiffAt_id.const_smul s⁻¹))

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ConeSlopeReciprocalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem coverC1BoundaryAt_physical_patch {A : Set Cover} (hA : MeasurableSet A)
    {p : Cover} (hp : p ∈ coverEssentialBoundary A) (hC : CoverC1BoundaryAt A p) :
    ∃ (a n : Cover) (g : Plane → ℝ) (R : ℝ) (U : Set Cover),
      ‖n‖ = 1 ∧ LipschitzWith (1/4) g ∧ 0 < R ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ Metric.ball a R ∧
      (∀ x ∈ U, x ∈ coverEssentialBoundary A ↔
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphSignedHeight a n g x < 0)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ 0 < graphSignedHeight a n g x))) := by
  obtain ⟨n,b,s,G,hn,hs,hb,hG,hGc,_,hcover⟩ := hC
  let a := p+s • b
  let g := dilatedGraph s G
  let R := 3*s/(544*8192)
  let r := s/(544*16384)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hg := dilatedGraph_lipschitz hG hs
  have hc (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) R) : ContDiffAt ℝ 1 g y := by
    apply dilatedGraph_contDiffAt
    apply hGc.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le]
    apply (inv_mul_lt_iff₀ hs).mpr
    have hh : ‖y‖ ≤ R := by simpa using hy
    dsimp only [R] at hh
    nlinarith
  have hba : Metric.ball p r ⊆ Metric.ball a R := by
    intro x hx
    have hd := dist_triangle x p a
    have hpa : dist p a = s*‖b‖ := by simp only [a,dist_eq_norm,sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hs.le]
    rw [hpa] at hd
    have hx' : dist x p < r := hx
    change dist x a < R
    dsimp only [R,r] at hx' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hb hs.le]
  have hbd (x : Cover) (hx : x ∈ Metric.ball p r) :
      x ∈ coverEssentialBoundary A ↔ normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
    let z := s⁻¹ • (x-p)
    have hz : z ∈ Metric.ball (0 : Cover) (1/(544*8192)) := by
      simp only [Metric.mem_ball,dist_zero_right,z,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le]
      apply (inv_mul_lt_iff₀ hs).mpr
      have hh : ‖x-p‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      dsimp only [r] at hh
      nlinarith
    have hxz : p+s • z=x := by simp only [z,smul_smul,mul_inv_cancel₀ hs.ne',one_smul,add_sub_cancel]
    have hxa : x-a=s • (z-b) := by
      simp only [a,z,smul_sub,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
      abel
    have he : normalGraph n g (normalPlaneCoordinates n (x-a)) =
        s • normalGraph n G (normalPlaneCoordinates n (z-b)) := by
      rw [normalGraph_dilated n G hs.ne',hxa,map_smul,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
    rw [he,hxa,smul_right_inj hs.ne']
    simpa only [hxz] using hcover z hz

  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases hA a hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (by simpa using hr)) hp (fun x hx hb ↦ (hbd x hx).mp hb)
  refine ⟨a,n,g,R,W,hn,hg,hR,hc,hW,hpW,hWU.trans hba,fun x hx ↦ hbd x (hWU hx),?_⟩
  exact hphase.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_neg_normal (F : Cover → Cover) (x v : Cover) :
    tangentialDivergence F x (-v)=tangentialDivergence F x v := by
  simp only [tangentialDivergence,map_neg,inner_neg_neg]

lemma reverseBlowupNormal_stationary (ν : FiniteMeasure BlowupNormalBundle)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (_hs : HasCompactSupport F) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle)) =
      ∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle) := by
  rw [FiniteMeasure.toMeasure_map,integral_map continuous_reverseBlowupNormal.measurable.aemeasurable
    (continuous_blowupTangentTest hF).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z ↦ tangentialDivergence_neg_normal F z.1 z.2)

lemma graph_superlevel_compl_ae {A U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : Continuous g)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫)) :
    ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ Aᶜ ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
  have hnz : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
    rw [ae_iff]
    simpa only [not_not] using graph_trace_volume_zero a hn hg
  filter_upwards [hgraph,hnz] with x hx hne hU
  rw [mem_compl_iff,hx hU,not_lt]
  exact ⟨fun h ↦ lt_of_le_of_ne h hne,le_of_lt⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem strict_C1_patch_stationary {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.closedBall (0 : Cover) 1})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {p : Cover} (hp : p ∈ coverEssentialBoundary A) (hpn : ‖p‖ < 1)
    (hC : CoverC1BoundaryAt A p) :
    ∃ (a n : Cover) (g : Plane → ℝ) (R ρ : ℝ),
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ 0<R ∧ 0<ρ ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      Metric.closedBall p (2*ρ) ⊆ Metric.ball a R ∧
      (∀ x ∈ Metric.closedBall p (2*ρ), x ∈ coverEssentialBoundary A ↔
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) ∧
      ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall p ρ →
        (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
          (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0 := by
  obtain ⟨a,n,g,R,U,hn,hg,hR,hc,hU,hpU,hUR,hbd,hphase⟩ :=
    coverC1BoundaryAt_physical_patch hA hp hC
  have hpB : p ∈ Metric.ball (0 : Cover) 1 := by simpa using hpn
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter Metric.isOpen_ball).mem_nhds ⟨hpU,hpB⟩)
  let ρ := r/3
  have hρ : 0<ρ := by dsimp only [ρ]; positivity
  have hsub : Metric.closedBall p (2*ρ) ⊆ U ∩ Metric.ball (0 : Cover) 1 := by
    apply Subset.trans _ hrsub
    exact Metric.closedBall_subset_ball (by dsimp only [ρ]; linarith)
  have hsubU := hsub.trans inter_subset_left
  have hsubO := hsub.trans (inter_subset_right.trans Metric.ball_subset_closedBall)
  refine ⟨a,n,g,R,ρ,hn,hg,hR,hρ,hc,hsubU.trans hUR,
    fun x hx ↦ hbd x (hsubU hx),?_⟩
  intro F hF hsF
  let φ := radialHeightCutoff p ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ ⊆ Metric.closedBall p (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hsubU
  have hφO := hφs.trans hsubO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x ∈ Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hφF (x : Cover) (hx : x ∈ tsupport F) : φ x=1 := radialHeightCutoff_one hρ (hsF hx)
  have hFs : HasCompactSupport F := (isCompact_closedBall p ρ).of_isClosed_subset isClosed_closure hsF
  have hFO : tsupport F ⊆ Metric.closedBall (0 : Cover) 1 :=
    hsF.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hsubO)
  have hdc (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hc y hy).continuousAt_fderiv (by norm_num)
  rcases hphase with hphase|hphase
  · have hp' : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
      filter_upwards [hphase] with x hx hU
      simpa only [graphSignedHeight,sub_neg] using hx hU
    exact blowup_C1graph_stationary hA a hn hg hdc hp' heq
      (fun F hF _ hs _ ↦ (hflux F hF hs).2) hφ hsφ hφU hφO hφR hφb
      hF hFs hφF (hflux F hF hFO).1
  · have hp' : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫) := by
      filter_upwards [hphase] with x hx hU
      simpa only [graphSignedHeight,sub_pos] using hx hU
    have hphase' := graph_superlevel_compl_ae a hn hg.continuous hp'
    have heq' := coverLocalPerimeter_normal_compl hA Metric.isClosed_closedBall.measurableSet heq
    have hflux' := fun (F : Cover → Cover) hF hFs hs hb ↦ reverseBlowupNormal_flux (F := F) hA
      (fun F hF _ hs _ ↦ (hflux F hF hs).2) hF hFs hs hb
    have hstat' : (∫ z, tangentialDivergence F z.1 z.2
        ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle))=0 := by
      rw [reverseBlowupNormal_stationary ν hF hFs]
      exact (hflux F hF hFO).1
    exact blowup_C1graph_stationary hA.compl a hn hg hdc hphase' heq' hflux'
      hφ hsφ hφU hφO hφR hφb hF hFs hφF hstat'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_tangent_graph {n : Cover} (hn : ‖n‖ = 1) (q : Plane) :
    normalPlaneCoordinates n (tangentPart (graphSlopeNormal n q) n) =
      (‖n-normalPlaneEmbedding n q‖⁻¹)^2 • q := by
  have hi : ⟪graphSlopeNormal n q,n⟫ = ‖n-normalPlaneEmbedding n q‖⁻¹ := by
    have hz : ⟪normalPlaneEmbedding n q,n⟫=0 :=
      (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn q)
    rw [graphSlopeNormal,real_inner_smul_left,inner_sub_left,real_inner_self_eq_norm_sq,hn,hz]
    ring
  rw [tangentPart,hi]
  simp only [map_sub,map_smul,normalPlaneCoordinates_normal hn,graphSlopeNormal,
    normalPlaneCoordinates_embedding,zero_sub,smul_neg,neg_neg,smul_smul,pow_two]

lemma graph_vertical_variation (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ) (y : Plane) :
    tangentialDivergence (fun x ↦ graphHeightExtension a n ψ x • n)
      (a+normalGraph n g y) (graphSlopeNormal n (gradient g y)) * ‖graphAreaVector n g y‖ =
      fderiv ℝ ψ y (gradient g y) / ‖graphAreaVector n g y‖ := by
  have hd : DifferentiableAt ℝ (graphHeightExtension a n ψ) (a+normalGraph n g y) :=
    ((hψ _).comp _ ((normalPlaneCoordinates n).differentiableAt.comp _
      (differentiableAt_id.sub_const a)))
  have hnz : ‖graphAreaVector n g y‖ ≠ 0 := by
    have hh := graphSlopeVector_norm_ge hn (gradient g y)
    exact ne_of_gt (by change 0 < ‖n-normalPlaneEmbedding n (gradient g y)‖; linarith)
  rw [tangentialDivergence_smul_const hd,graphHeightExtension_fderiv a n hψ,
    ContinuousLinearMap.comp_apply,normalPlaneCoordinates_tangent_graph hn,
    add_sub_cancel_left,normalPlaneCoordinates_graph hn,map_smul]
  change (‖graphAreaVector n g y‖⁻¹)^2 * fderiv ℝ ψ y (gradient g y) *
      ‖graphAreaVector n g y‖ = _
  field_simp

lemma radialHeightCutoff_eventually_one {p : Cover} {r : ℝ} (hr : 0 < r)
    {x : Cover} (hx : x ∈ Metric.ball p r) :
    radialHeightCutoff p r =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
  exact radialHeightCutoff_one hr (Metric.ball_subset_closedBall hz)

theorem stationary_graph_weak_equation (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {p : Cover} {ρ : ℝ} (hρ : 0<ρ)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : ∀ y ∈ tsupport ψ, a+normalGraph n g y ∈ Metric.ball p (ρ/2)) :
    (∫ y : Plane, fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖)=0 := by
  let ζ := radialHeightCutoff p (ρ/2)
  let f := graphHeightExtension a n ψ
  let F : Cover → Cover := fun x ↦ (ζ x*f x) • n
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := radialDensityWeight_contDiff _ _ _
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := graphHeightExtension_contDiff a n hψ
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hζ.mul hf).smul contDiff_const
  have hsF : tsupport F ⊆ Metric.closedBall p ρ := by
    have hsζ : tsupport ζ ⊆ Metric.closedBall p ρ := by
      have hh := radialDensityWeight_tsupport (a := p) (r := 2*(ρ/2))
        (ε := 3*(ρ/2)^2) (by positivity) (by positivity)
      convert hh using 1 <;> congr 1; ring
    apply Subset.trans _ hsζ
    apply closure_mono
    intro x hx
    by_contra hh
    exact hx (by simp [F,Function.notMem_support.mp hh])
  have he (y : Plane) : tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖ =
      fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖ := by
    let x := a+normalGraph n g y
    have hxy : normalPlaneCoordinates n (x-a)=y := by
      simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    by_cases hy : y ∈ tsupport ψ
    · have hz : ζ =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
        radialHeightCutoff_eventually_one (by positivity) (hsψ y hy)
      have hFe : F =ᶠ[𝓝 x] (fun z ↦ f z • n) := by
        filter_upwards [hz] with z hz
        simp only [F,hz,one_mul]
      have hde := hFe.fderiv_eq (𝕜 := ℝ)
      have hte : tangentialDivergence F x (graphSlopeNormal n (gradient g y)) =
          tangentialDivergence (fun z ↦ f z • n) x (graphSlopeNormal n (gradient g y)) := by
        simp only [tangentialDivergence,divergence,hde]
      change tangentialDivergence F x _ * _ = _
      rw [hte]
      exact graph_vertical_variation a hn g (hψ.differentiable (by simp)) y
    · have hψ0 : ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hy
      have hf0 : f =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
        have hp := ((normalPlaneCoordinates n).continuous.comp (continuous_id.sub (continuous_const (y := a)))).tendsto x
        change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x)
          (𝓝 (normalPlaneCoordinates n (x-a))) at hp
        rw [hxy] at hp
        exact hp.eventually hψ0
      have hF0 : F =ᶠ[𝓝 x] (fun _ ↦ (0 : Cover)) := by
        filter_upwards [hf0] with z hz
        simp only [F,hz,mul_zero,zero_smul]
      have hd0 := hF0.fderiv_eq (𝕜 := ℝ)
      have hψd0 := hψ0.fderiv_eq (𝕜 := ℝ)
      change tangentialDivergence F x _ * _ = _
      simp [tangentialDivergence,divergence,hd0,hψd0]
  simpa only [he] using hstat F hF hsF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_cone_boundary_smul {A : Set Cover}
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {x : Cover} (hx : x ∈ coverEssentialBoundary A) (hxb : ‖x‖<1)
    {s : ℝ} (hs : 0 < s) (hs1 : s≤1) : s • x ∈ coverEssentialBoundary A := by
  have hinv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have he : ∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) 1 →
      (y ∈ A ↔ y ∈ (fun z : Cover ↦ s • z) ⁻¹' A) := by
    filter_upwards [hcone s⁻¹ hinv] with y hy hb
    simpa only [inv_inv,mem_preimage] using (hy hb).symm
  have hpre := cover_boundary_local_ae
    (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Cover) 1 by simpa using hxb)) he hx
  exact cover_boundary_preimage_image (Measure.quasiMeasurePreserving_smul volume hs.ne')
    (show ContinuousAt (fun z : Cover ↦ s • z) x from (Continuous.const_smul continuous_id s).continuousAt) hpre

theorem cone_graph_radial_derivative {A : Set Cover}
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {x a n : Cover} (hn : ‖n‖=1) (hx : x ∈ coverEssentialBoundary A) (hxb : ‖x‖<1)
    {g : Plane → ℝ}
    (hg : DifferentiableAt ℝ g (normalPlaneCoordinates n (x-a)))
    (hgraph : ∀ᶠ z in 𝓝 x, z ∈ coverEssentialBoundary A →
      normalGraph n g (normalPlaneCoordinates n (z-a))=z-a) :
    fderiv ℝ g (normalPlaneCoordinates n (x-a)) (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  have htx : Tendsto (fun t : ℝ ↦ t • x) (𝓝 (1 : ℝ)) (𝓝 x) := by
    have hh : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
    simpa only [one_smul] using hh.tendsto (1 : ℝ)
  have he : (fun t : ℝ ↦ g (normalPlaneCoordinates n (t • x-a))) =ᶠ[𝓝[≤] (1 : ℝ)]
      (fun t ↦ ⟪n,t • x-a⟫) := by
    filter_upwards [htx.eventually hgraph |> mem_nhdsWithin_of_mem_nhds,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)), self_mem_nhdsWithin] with t ht ht0 ht1
    have hb := ht (cover_cone_boundary_smul hcone hx hxb ht0 ht1)
    have hh := congrArg (fun v : Cover ↦ ⟪n,v⟫) hb
    simpa only [normalGraph_inner hn] using hh
  have hlin : HasDerivAt (fun t : ℝ ↦ t • x-a) x 1 := by
    simpa using (((hasDerivAt_id (1 : ℝ)).smul_const x).sub_const a)
  have hdlin : HasDerivAt (fun t : ℝ ↦ normalPlaneCoordinates n (t • x-a))
      (normalPlaneCoordinates n x) 1 :=
    (normalPlaneCoordinates n).hasFDerivAt.comp_hasDerivAt 1 hlin
  have hg' : DifferentiableAt ℝ g (normalPlaneCoordinates n ((1 : ℝ) • x-a)) := by
    simpa only [one_smul] using hg
  have hdg' : HasDerivAt (fun t : ℝ ↦ g (normalPlaneCoordinates n (t • x-a)))
      (fderiv ℝ g (normalPlaneCoordinates n (x-a)) (normalPlaneCoordinates n x)) 1 := by
    simpa only [Function.comp_def,one_smul] using hg'.hasFDerivAt.comp_hasDerivAt 1 hdlin
  have hdi : HasDerivAt (fun t : ℝ ↦ ⟪n,t • x-a⟫) ⟪n,x⟫ 1 :=
    (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt 1 hlin
  have hval : g (normalPlaneCoordinates n ((1 : ℝ) • x-a)) = ⟪n,(1 : ℝ) • x-a⟫ :=
    he.self_of_nhdsWithin (by simp : (1 : ℝ) ∈ Iic (1 : ℝ))
  exact (hdg'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 1)).symm.trans
    ((hdi.hasDerivWithinAt.congr_of_eventuallyEq he hval).derivWithin
      (uniqueDiffWithinAt_Iic 1))

lemma cone_graph_radial_projection_ne_zero {x n : Cover} (hn : ‖n‖=1)
    (hx : x≠0) {L : Plane →L[ℝ] ℝ} (he : L (normalPlaneCoordinates n x)=⟪n,x⟫) :
    normalPlaneCoordinates n x ≠ 0 := by
  intro hz
  have hi : ⟪n,x⟫=0 := by rw [hz,map_zero] at he; exact he.symm
  have hh := normalPlaneCoordinates_reconstruct hn x
  rw [hz,hi] at hh
  have h0 : normalPlaneEmbedding n 0=0 := by
    apply norm_eq_zero.mp
    simpa using normalPlaneEmbedding_norm n (0 : Plane)
  exact hx (by simpa only [h0,zero_smul,add_zero] using hh.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeScalarTest_derivative {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) {r s : ℝ} (hr : r≠0) (v : Plane) :
    fderiv ℝ (slopeScalarTest χ ψ) (planarWedgeChart (r,s)) v =
      deriv χ r*ψ s*(planeProductCoordinates v).1 +
        χ r*deriv ψ s*((planeProductCoordinates v).2-s*(planeProductCoordinates v).1)/r := by
  let x := planarWedgeChart (r,s)
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ ↦ slopeScalarTest χ ψ (x+t • v))
      (fderiv ℝ (slopeScalarTest χ ψ) x v) 0 := by
    simpa only [zero_smul,add_zero,Function.comp_def] using
      ((hf.differentiable (by simp)) (x+(0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he (t : ℝ) : slopeScalarTest χ ψ (x+t • v)=
      χ (r+t*(planeProductCoordinates v).1)*
        ψ ((r*s+t*(planeProductCoordinates v).2)/(r+t*(planeProductCoordinates v).1)) := by
    simp [slopeScalarTest,x,planarWedgeChart]
  simp_rw [he] at hd
  have hd₁ : HasDerivAt (fun t : ℝ ↦ r+t*(planeProductCoordinates v).1)
      (planeProductCoordinates v).1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (planeProductCoordinates v).1).const_add r
  have hd₂ : HasDerivAt (fun t : ℝ ↦ r*s+t*(planeProductCoordinates v).2)
      (planeProductCoordinates v).2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (planeProductCoordinates v).2).const_add (r*s)
  have hden : r+(0 : ℝ)*(planeProductCoordinates v).1≠0 := by simpa using hr
  have hquot := hd₂.div hd₁ hden
  have hc := (((hχ.differentiable (by simp)) _).hasDerivAt.comp 0 hd₁)
  have hp := (((hψ.differentiable (by simp)) _).hasDerivAt.comp 0 hquot)
  have hh := hd.unique (hc.mul hp)
  simp only [Function.comp_apply,Pi.div_apply,zero_mul,add_zero,mul_div_cancel_left₀ _ hr] at hh
  change _ = _ at hh
  rw [hh]
  field_simp

lemma integral_mul_deriv_radial {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ) :
    (∫ r : ℝ, r*deriv χ r)=-(∫ r : ℝ, χ r) := by
  have hχd : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hi : Integrable (fun r : ℝ ↦ r*deriv χ r) :=
    (continuous_id.mul hχd).integrable_of_hasCompactSupport hsχ.deriv.mul_left
  have hj : Integrable (fun r : ℝ ↦ (1 : ℝ)*χ r) := by
    simpa only [one_mul] using hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hk : Integrable (fun r : ℝ ↦ r*χ r) :=
    (continuous_id.mul hχ.continuous).integrable_of_hasCompactSupport hsχ.mul_left
  simpa only [one_mul,id_eq] using integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun r _ ↦ hasDerivAt_id r) (fun r _ ↦ ((hχ.differentiable (by simp)) r).hasDerivAt) hi hj hk

theorem integral_slope_separated {G : Plane → ℝ} (hG : Integrable G)
    {χ A B : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : HasCompactSupport χ) (hχpos : tsupport χ ⊆ Ioi (0 : ℝ))
    (hA : Integrable A) (hB : Integrable B)
    (hzero : ∀ r : ℝ, r≤0 → ∀ y : ℝ, G (planeProductCoordinates.symm (r,y))=0)
    (he : ∀ r : ℝ, 0 < r → ∀ s : ℝ, G (planarWedgeChart (r,s))=
      deriv χ r*A s+(χ r/r)*B s) :
    (∫ y : Plane, G y)=(∫ r : ℝ, χ r)*((∫ s : ℝ, B s)-(∫ s : ℝ, A s)) := by
  have hL := planeProductCoordinates_measurePreserving.symm
    planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLi := (hL.integrable_comp hG.aestronglyMeasurable).mpr hG
  have hi : (fun r : ℝ ↦ ∫ y : ℝ, G (planeProductCoordinates.symm (r,y))) =
      (fun r : ℝ ↦ (r*deriv χ r)*(∫ s : ℝ, A s)+χ r*(∫ s : ℝ, B s)) := by
    funext r
    by_cases hr : 0 < r
    · have hscale : (∫ y : ℝ, G (planeProductCoordinates.symm (r,y))) =
          r*(∫ s : ℝ, G (planarWedgeChart (r,s))) := by
        change _ = r*(∫ s : ℝ, G (planeProductCoordinates.symm (r,r*s)))
        rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ G (planeProductCoordinates.symm (r,y))) r,
          abs_of_pos (inv_pos.mpr hr),smul_eq_mul,mul_inv_cancel_left₀ hr.ne']
      rw [hscale]
      simp_rw [he r hr]
      rw [integral_add (hA.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul]
      field_simp
    · have hz : r ∉ tsupport χ := fun hh ↦ hr (hχpos hh)
      simp only [hzero r (le_of_not_gt hr),integral_zero,
        image_eq_zero_of_notMem_tsupport hz,deriv_of_notMem_tsupport hz,mul_zero,zero_mul,add_zero]
  have hχi : Integrable χ (volume : Measure ℝ) := hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hχdi : Integrable (fun r : ℝ ↦ r*deriv χ r) :=
    (continuous_id.mul (hχ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsχ.deriv.mul_left
  rw [← hL.integral_comp planeProductCoordinates.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding G]
  change (∫ z : ℝ × ℝ, G (planeProductCoordinates.symm z)) = _
  change Integrable (fun z : ℝ × ℝ ↦ G (planeProductCoordinates.symm z)) (volume.prod volume) at hLi
  rw [Measure.volume_eq_prod,integral_prod _ hLi,hi,
    integral_add (hχdi.mul_const _) (hχi.mul_const _),integral_mul_const,integral_mul_const,
    integral_mul_deriv_radial hχ hsχ]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma continuous_mul_shift_integrable {u b : ℝ → ℝ} (hu : Continuous u)
    (hb : Continuous b) (hs : HasCompactSupport b) (x : ℝ) :
    Integrable (fun t ↦ u t*b (t-x)) := by
  have hb' : HasCompactSupport (fun t ↦ b (t-x)) := by
    have hh := hs.comp_homeomorph (Homeomorph.addRight (-x))
    change HasCompactSupport (fun t : ℝ ↦ b (t+ -x)) at hh
    simpa only [sub_eq_add_neg] using hh
  exact (hu.mul (hb.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport hb'.mul_left

lemma continuous_angular_smoothing_tendsto {u : ℝ → ℝ} (hu : Continuous u) (x : ℝ) :
    Tendsto (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-x)) atTop (𝓝 (u x)) := by
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) angularMollifier_radius_tendsto hu x
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change u t*(angularMollifier i).normed volume (t-x) =
    (angularMollifier i).normed volume (x-t)*u t
  rw [show x-t = -(t-x) by ring,(angularMollifier i).normed_neg]
  ring

theorem continuous_constant_of_weak_derivative_zero {u : ℝ → ℝ} (hu : Continuous u)
    {a b x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t)=0) : u x=u y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  have hrad : ∀ᶠ i : ℕ in atTop, (angularMollifier i).rOut < min (x-a) (b-y) :=
    angularMollifier_radius_tendsto.eventually (gt_mem_nhds (by exact lt_min (by linarith [hx.1]) (by linarith [hy.2])))
  have he : (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-x)) =ᶠ[atTop]
      (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-y)) := by
    filter_upwards [hrad] with i hi
    let k := (angularMollifier i).normed volume
    have hk : ContDiff ℝ (⊤ : ℕ∞) k := (angularMollifier i).contDiff_normed
    have hks : tsupport k ⊆ Icc (-(angularMollifier i).rOut) (angularMollifier i).rOut := by
      rw [(angularMollifier i).tsupport_normed_eq,Real.closedBall_eq_Icc]
      simp only [zero_sub,zero_add,subset_refl]
    have hs : tsupport (intervalSmoothHat k x y) ⊆ Ioo a b := by
      apply (intervalSmoothHat_support hk.continuous hks hxy).trans
      intro t ht
      constructor <;> linarith [lt_of_lt_of_le hi (min_le_left _ _),lt_of_lt_of_le hi (min_le_right _ _),ht.1,ht.2]
    have hh := hweak (intervalSmoothHat k x y) (intervalSmoothHat_contDiff hk x y) hs
    simp_rw [(intervalSmoothHat_hasDerivAt hk.continuous x y _).deriv,mul_sub] at hh
    rw [integral_sub (continuous_mul_shift_integrable hu hk.continuous
      (angularMollifier i).hasCompactSupport_normed x)
      (continuous_mul_shift_integrable hu hk.continuous (angularMollifier i).hasCompactSupport_normed y)] at hh
    exact sub_eq_zero.mp hh
  exact tendsto_nhds_unique (continuous_angular_smoothing_tendsto hu x)
    ((continuous_angular_smoothing_tendsto hu y).congr' he.symm)

theorem hasDerivAt_of_continuous_weak_derivative {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {a b : ℝ}
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t) = -(∫ t : ℝ, v t*ψ t))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt u (v x) x := by
  let V : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, v s
  have hd (t : ℝ) : HasDerivAt V (v t) t := intervalIntegral.integral_hasDerivAt_right
    (hv.intervalIntegrable 0 t) (hv.stronglyMeasurableAtFilter volume _) hv.continuousAt
  have hV : Continuous V := (fun t ↦ (hd t).continuousAt) |> continuous_iff_continuousAt.mpr
  have hz : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, (u t-V t)*deriv ψ t)=0 := by
    intro ψ hψ hsψ
    have hs : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hsψ.trans Ioo_subset_Icc_self)
    have hψd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hui : Integrable (fun t ↦ u t*deriv ψ t) :=
      (hu.mul hψd).integrable_of_hasCompactSupport hs.deriv.mul_left
    have hVi : Integrable (fun t ↦ V t*deriv ψ t) :=
      (hV.mul hψd).integrable_of_hasCompactSupport hs.deriv.mul_left
    have hvi : Integrable (fun t ↦ v t*ψ t) :=
      (hv.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hprod : Integrable (fun t ↦ V t*ψ t) :=
      (hV.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ ↦ hd t) (fun t _ ↦ ((hψ.differentiable (by simp)) t).hasDerivAt) hVi hvi hprod
    simp_rw [sub_mul]
    rw [integral_sub hui hVi,hweak ψ hψ hsψ,hparts,sub_self]
  have he : u =ᶠ[𝓝 x] (fun t ↦ V t+(u x-V x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    have hh := continuous_constant_of_weak_derivative_zero (hu.sub hV) ht hx hz
    dsimp only [Pi.sub_apply] at hh
    linarith
  exact ((hd x).add_const (u x-V x)).congr_of_eventuallyEq he

theorem hasDerivAt_of_continuousOn_weak_derivative {u v : ℝ → ℝ}
    {a b : ℝ} (hu : ContinuousOn u (Ioo a b)) (hv : ContinuousOn v (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t) = -(∫ t : ℝ, v t*ψ t))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt u (v x) x := by
  let c := (a+x)/2
  let d := (x+b)/2
  have hcx : c<x := by dsimp only [c]; linarith [hx.1]
  have hxd : x<d := by dsimp only [d]; linarith [hx.2]
  have hsub : Icc c d ⊆ Ioo a b := by
    intro t ht
    constructor <;> dsimp only [c,d] at ht <;> linarith [ht.1,ht.2,hx.1,hx.2]
  let U : C(Icc c d,ℝ) := ⟨fun t ↦ u t,continuousOn_iff_continuous_domRestrict.mp (hu.mono hsub)⟩
  let W : C(Icc c d,ℝ) := ⟨fun t ↦ v t,continuousOn_iff_continuous_domRestrict.mp (hv.mono hsub)⟩
  obtain ⟨U',hU'⟩ := U.exists_extension' isClosed_Icc.isClosedEmbedding_subtypeVal
  obtain ⟨W',hW'⟩ := W.exists_extension' isClosed_Icc.isClosedEmbedding_subtypeVal
  have heU (t : ℝ) (ht : t ∈ Icc c d) : U' t=u t := congrFun hU' ⟨t,ht⟩
  have heW (t : ℝ) (ht : t ∈ Icc c d) : W' t=v t := congrFun hW' ⟨t,ht⟩
  have hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo c d →
      (∫ t : ℝ, U' t*deriv ψ t) = -(∫ t : ℝ, W' t*ψ t) := by
    intro ψ hψ hsψ
    have he₁ : (fun t ↦ U' t*deriv ψ t) = (fun t ↦ u t*deriv ψ t) := by
      funext t
      by_cases ht : t ∈ tsupport ψ
      · rw [heU t (Ioo_subset_Icc_self (hsψ ht))]
      · rw [deriv_of_notMem_tsupport ht,mul_zero,mul_zero]
    have he₂ : (fun t ↦ W' t*ψ t) = (fun t ↦ v t*ψ t) := by
      funext t
      by_cases ht : t ∈ tsupport ψ
      · rw [heW t (Ioo_subset_Icc_self (hsψ ht))]
      · rw [image_eq_zero_of_notMem_tsupport ht,mul_zero,mul_zero]
    rw [he₁,he₂]
    exact hweak ψ hψ (hsψ.trans (Ioo_subset_Icc_self.trans hsub))
  have hd := hasDerivAt_of_continuous_weak_derivative U'.continuous W'.continuous hw ⟨hcx,hxd⟩
  rw [heW x ⟨hcx.le,hxd.le⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo c d from ⟨hcx,hxd⟩)] with t ht
  exact (heU t (Ioo_subset_Icc_self ht)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

theorem cone_slope_ODE_derivative {f q c h : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hc : ContinuousOn c (Ioo a b))
    (hpos : ∀ s ∈ Ioo a b, 0 < c s)
    (hmetric : ∀ s ∈ Ioo a b, (c s)^2*(1+(f s-s*q s)^2+(q s)^2)=1)
    (hflux : ∀ s ∈ Ioo a b, h s=(q s-s*(f s-s*q s))*c s)
    (hh : ∀ s ∈ Ioo a b, HasDerivAt h (-(f s-s*q s)*c s) s)
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt q 0 x ∧ HasDerivAt c 0 x := by
  have hcx := hpos x hx
  have hden (s : ℝ) : 0<1+s^2+(f s)^2 := by positivity
  have hid (s : ℝ) (hs : s ∈ Ioo a b) :
      1+s^2-(h s)^2=(c s)^2*(1+s^2+(f s)^2) := by
    rw [hflux s hs]
    linear_combination -(1+s^2)*(hmetric s hs)
  have hhnum : 2*x+2*(h x)*(f x-x*q x)*c x = (c x)^2*(2*x+2*f x*q x) := by
    rw [hflux x hx]
    linear_combination -(2*x)*(hmetric x hx)
  have hdnum : HasDerivAt (fun s ↦ 1+s^2-(h s)^2)
      (2*x+2*(h x)*(f x-x*q x)*c x) x := by
    convert (((hasDerivAt_id x).pow 2).const_add 1).sub ((hh x hx).pow 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hdden : HasDerivAt (fun s ↦ 1+s^2+(f s)^2) (2*x+2*f x*q x) x := by
    convert (((hasDerivAt_id x).pow 2).const_add 1).add ((hf x hx).pow 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hdsq : HasDerivAt (fun s ↦ (c s)^2) 0 x := by
    have hd := hdnum.div hdden (hden x).ne'
    rw [hhnum,hid x hx] at hd
    have he : (fun s ↦ (c s)^2) =ᶠ[𝓝 x]
        (fun s ↦ (1+s^2-(h s)^2)/(1+s^2+(f s)^2)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hid s hs,mul_div_cancel_right₀ _ (hden s).ne']
    convert hd.congr_of_eventuallyEq he using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (field_simp; ring)
  have hdc : HasDerivAt c 0 x := by
    have hd := hdsq.sqrt (by positivity : (c x)^2 ≠ 0)
    have he : c =ᶠ[𝓝 x] (fun s ↦ Real.sqrt ((c s)^2)) := by
      filter_upwards [(hc.continuousAt (isOpen_Ioo.mem_nhds hx)).eventually
        (Ioi_mem_nhds hcx)] with s hs
      rw [Real.sqrt_sq hs.le]
    simpa only [zero_div] using hd.congr_of_eventuallyEq he
  have hqeq (s : ℝ) (hs : s ∈ Ioo a b) :
      q s=(h s+s*f s*c s)/((1+s^2)*c s) := by
    rw [hflux s hs]
    field_simp [(hpos s hs).ne']
    ring
  have hn : HasDerivAt (fun s ↦ h s+s*f s*c s)
      (2*x*q x*c x) x := by
    convert (hh x hx).add ((((hasDerivAt_id x).mul (hf x hx)).mul hdc)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hd : HasDerivAt (fun s ↦ (1+s^2)*c s) (2*x*c x) x := by
    convert ((((hasDerivAt_id x).pow 2).const_add 1).mul hdc) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hneq : (1+x^2)*c x≠0 := by positivity
  have hder := hn.div hd hneq
  have he : q =ᶠ[𝓝 x] (fun s ↦ (h s+s*f s*c s)/((1+s^2)*c s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact hqeq s hs
  refine ⟨?_,hdc⟩
  convert hder.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (rw [hflux x hx]; field_simp; ring)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

lemma coneSlopeReciprocalArea_pos (f q : ℝ → ℝ) (s : ℝ) :
    0 < coneSlopeReciprocalArea f q s := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

lemma coneSlopeReciprocalArea_metric (f q : ℝ → ℝ) (s : ℝ) :
    (coneSlopeReciprocalArea f q s)^2*(1+(f s-s*q s)^2+(q s)^2)=1 := by
  have hp : 0<1+(f s-s*q s)^2+(q s)^2 := by positivity
  dsimp only [coneSlopeReciprocalArea]
  rw [inv_pow,Real.sq_sqrt hp.le,inv_mul_cancel₀ hp.ne']

lemma coneSlopeReciprocalArea_continuousOn {f q : ℝ → ℝ} {U : Set ℝ}
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) :
    ContinuousOn (coneSlopeReciprocalArea f q) U := by
  apply ((((hf.sub (continuousOn_id.mul hq)).pow 2).const_add 1).add (hq.pow 2)).sqrt.inv₀
  intro s hs
  exact (Real.sqrt_pos.2 (by positivity : 0<1+(f s-s*q s)^2+(q s)^2)).ne'

theorem weak_cone_slope_derivative {f q : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hq : ContinuousOn q (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ s : ℝ, coneSlopeFlux f q s*deriv ψ s) =
        (∫ s : ℝ, (f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt q 0 x := by
  have hfc : ContinuousOn f (Ioo a b) := fun s hs ↦ (hf s hs).continuousAt.continuousWithinAt
  have hc := coneSlopeReciprocalArea_continuousOn hfc hq
  have hu := hfc.sub (continuousOn_id.mul hq)
  have hh : ContinuousOn (coneSlopeFlux f q) (Ioo a b) :=
    (hq.sub (continuousOn_id.mul hu)).mul hc
  have hhder (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (coneSlopeFlux f q) (-(f s-s*q s)*coneSlopeReciprocalArea f q s) s := by
    apply hasDerivAt_of_continuousOn_weak_derivative hh (hu.neg.mul hc) _ hs
    intro ψ hψ hsψ
    rw [hweak ψ hψ hsψ]
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.neg_apply,id_eq,neg_mul,integral_neg,neg_neg]
  exact (cone_slope_ODE_derivative hf hc
    (fun s _ ↦ coneSlopeReciprocalArea_pos f q s)
    (fun s _ ↦ coneSlopeReciprocalArea_metric f q s)
    (fun s _ ↦ rfl) hhder hx).1

theorem weak_cone_slope_affine {f q : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hq : ContinuousOn q (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ s : ℝ, coneSlopeFlux f q s*deriv ψ s) =
        (∫ s : ℝ, (f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s))
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    q y=q x ∧ f y=f x+q x*(y-x) := by
  have hqd (s : ℝ) (hs : s ∈ Ioo a b) := weak_cone_slope_derivative hf hq hweak hs
  have hqc (s : ℝ) (hs : s ∈ Ioo a b) : q s=q x :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs ↦ (hqd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hqd s hs).deriv) hs hx
  have hfd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt (fun t ↦ f t-q x*t) 0 s := by
    have hd := (hf s hs).sub ((hasDerivAt_id s).const_mul (q x))
    convert hd using 1 <;> first | rfl | simp only [hqc s hs,mul_one,sub_self]
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun s hs ↦ (hfd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hfd s hs).deriv) hy hx
  exact ⟨hqc y hy,by change f y-q x*y=f x-q x*x at he; linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_coordinates (u v : Plane) :
    ⟪u,v⟫ = (planeProductCoordinates u).1*(planeProductCoordinates v).1+
      (planeProductCoordinates u).2*(planeProductCoordinates v).2 := by
  simp [planeProductCoordinates_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,Fin.sum_univ_two,mul_comm]

lemma plane_gradient_coordinates (g : Plane → ℝ) (y : Plane) :
    (planeProductCoordinates (gradient g y)).1 = fderiv ℝ g y slopeHorizontalVector ∧
    (planeProductCoordinates (gradient g y)).2 = fderiv ℝ g y slopeVerticalVector := by
  constructor <;> rw [← inner_gradient_left,plane_inner_coordinates]
  · simp [slopeHorizontalVector]
  · simp [slopeVerticalVector]

lemma planarWedgeChart_hasDerivAt_radial (r s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ planarWedgeChart (t,s))
      (planeProductCoordinates.symm (1,s)) r := by
  have hd := (hasDerivAt_id r).prodMk ((hasDerivAt_id r).mul_const s)
  convert planeProductCoordinates.symm.hasFDerivAt.comp_hasDerivAt r hd using 1 <;>
    first | rfl | simp only [one_mul,ContinuousLinearEquiv.coe_coe]

lemma planarWedgeChart_hasDerivAt_angular (r s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ planarWedgeChart (r,t)) (r • slopeVerticalVector) s := by
  have hd := (hasDerivAt_const s r).prodMk ((hasDerivAt_id s).const_mul r)
  have hh := planeProductCoordinates.symm.hasFDerivAt.comp_hasDerivAt s hd
  simpa [Function.comp_def,planarWedgeChart,slopeVerticalVector,← map_smul] using hh

theorem euler_graph_homogeneous {g : Plane → ℝ} {a b c d : ℝ} (ha : 0<a)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    {r t s : ℝ} (hr : r ∈ Ioo a b) (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d) :
    g (planarWedgeChart (r,s))/r=g (planarWedgeChart (t,s))/t := by
  have hd (v : ℝ) (hv : v ∈ Ioo a b) :
      HasDerivAt (fun w : ℝ ↦ g (planarWedgeChart (w,s))/w) 0 v := by
    have hv0 : 0<v := ha.trans hv.1
    have h := (hg v hv s hs).hasFDerivAt.comp_hasDerivAt v (planarWedgeChart_hasDerivAt_radial v s)
    have hh := h.div (hasDerivAt_id v) hv0.ne'
    have hmult : fderiv ℝ g (planarWedgeChart (v,s)) (planeProductCoordinates.symm (1,s))*v=
        g (planarWedgeChart (v,s)) := by
      calc
        _ = fderiv ℝ g (planarWedgeChart (v,s)) (v • planeProductCoordinates.symm (1,s)) := by
          rw [map_smul,smul_eq_mul,mul_comm]
        _ = _ := by
          rw [← map_smul]
          simpa [planarWedgeChart] using he v hv s hs
    convert hh using 1 <;> first | rfl | simp only [id_eq,Function.comp_def,hmult,mul_one,sub_self,zero_div]
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun v hv ↦ (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv ↦ (hd v hv).deriv) hr ht

lemma graph_angular_slice_hasDerivAt {g : Plane → ℝ} {r s : ℝ} (hr : r≠0)
    (hg : DifferentiableAt ℝ g (planarWedgeChart (r,s))) :
    HasDerivAt (fun t : ℝ ↦ g (planarWedgeChart (r,t))/r)
      (fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector) s := by
  have hd := (hg.hasFDerivAt.comp_hasDerivAt s
    (planarWedgeChart_hasDerivAt_angular r s)).div_const r
  simpa only [Function.comp_def,map_smul,smul_eq_mul,mul_div_cancel_left₀ _ hr] using hd

lemma planarWedgeChart_expand (r s : ℝ) :
    planarWedgeChart (r,s)=r • slopeHorizontalVector+(r*s) • slopeVerticalVector := by
  apply planeProductCoordinates.injective
  simp [planarWedgeChart,slopeHorizontalVector,slopeVerticalVector]

theorem euler_graph_gradient {g : Plane → ℝ} {a b c d : ℝ} (ha : 0<a)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    {r r₀ s : ℝ} (hr : r ∈ Ioo a b) (hr₀ : r₀ ∈ Ioo a b) (hs : s ∈ Ioo c d) :
    let f := g (planarWedgeChart (r₀,s))/r₀
    let q := fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector
    planeProductCoordinates (gradient g (planarWedgeChart (r,s)))=(f-s*q,q) := by
  dsimp only
  have hr0 : r≠0 := (ha.trans hr.1).ne'
  have hr₀0 : r₀≠0 := (ha.trans hr₀.1).ne'
  have hvs : fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector =
      fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector := by
    have hfun : (fun t : ℝ ↦ g (planarWedgeChart (r,t))/r) =ᶠ[𝓝 s]
        (fun t : ℝ ↦ g (planarWedgeChart (r₀,t))/r₀) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact euler_graph_homogeneous ha hg he hr hr₀ ht
    exact (graph_angular_slice_hasDerivAt hr0 (hg r hr s hs)).unique
      ((graph_angular_slice_hasDerivAt hr₀0 (hg r₀ hr₀ s hs)).congr_of_eventuallyEq hfun)
  have hre := he r hr s hs
  have hlin : fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s)) =
      r*fderiv ℝ g (planarWedgeChart (r,s)) slopeHorizontalVector+
        (r*s)*fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector := by
    calc
      _ = fderiv ℝ g (planarWedgeChart (r,s))
          (r • slopeHorizontalVector+(r*s) • slopeVerticalVector) :=
        congrArg (fderiv ℝ g (planarWedgeChart (r,s))) (planarWedgeChart_expand r s)
      _ = _ := by simp only [map_add,map_smul,smul_eq_mul]
  rw [hlin,hvs] at hre
  have hhom := euler_graph_homogeneous ha hg he hr hr₀ hs
  have hhom' : g (planarWedgeChart (r,s)) =
      (g (planarWedgeChart (r₀,s))/r₀)*r := (div_eq_iff hr0).mp hhom
  have hh : fderiv ℝ g (planarWedgeChart (r,s)) slopeHorizontalVector=
      g (planarWedgeChart (r₀,s))/r₀-s*fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector := by
    apply (mul_right_inj' hr0).mp
    nlinarith [hre,hhom']
  have hcoord := plane_gradient_coordinates g (planarWedgeChart (r,s))
  exact Prod.ext (hcoord.1.trans hh) (hcoord.2.trans hvs)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_norm_sqrt {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ = Real.sqrt (1+‖gradient g y‖^2) := by
  rw [plane_gradient_norm,← graphAreaVector_norm_sq hn g y,Real.sqrt_sq (norm_nonneg _)]

lemma minimalGraphDensity_tsupport (g ψ : Plane → ℝ) :
    tsupport (minimalGraphDensity g ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hh
  exact hy (by simp [minimalGraphDensity,fderiv_of_notMem_tsupport ℝ hh])

lemma minimalGraphDensity_integrable {g ψ : Plane → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ)
    (hg : ∀ y ∈ tsupport ψ, ContinuousAt (fderiv ℝ g) y) :
    Integrable (minimalGraphDensity g ψ) := by
  have hc : Continuous (minimalGraphDensity g ψ) := by
    apply continuous_of_tsupport
    intro y hy
    have hd := hg y (minimalGraphDensity_tsupport g ψ hy)
    have hgrad : ContinuousAt (gradient g) y :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hd
    exact ((hψ.continuous_fderiv (by simp)).continuousAt.clm_apply hgrad).div
      ((hgrad.norm.pow 2).const_add 1).sqrt
      (Real.sqrt_pos.2 (by positivity : 0<1+‖gradient g y‖^2)).ne'
  exact hc.integrable_of_hasCompactSupport
    (hsψ.of_isClosed_subset isClosed_closure (minimalGraphDensity_tsupport g ψ))

lemma continuous_mul_on_tsupport {f ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hf : ∀ s ∈ tsupport ψ, ContinuousAt f s) : Continuous (fun s ↦ f s*ψ s) := by
  apply continuous_of_tsupport
  intro s hs
  exact (hf s (tsupport_mul_subset_right hs)).mul hψ.continuousAt

lemma integrable_mul_on_tsupport {f ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hsψ : HasCompactSupport ψ) (hf : ∀ s ∈ tsupport ψ, ContinuousAt f s) :
    Integrable (fun s ↦ f s*ψ s) :=
  (continuous_mul_on_tsupport hψ hf).integrable_of_hasCompactSupport hsψ.mul_left

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarWedgeChart_continuous : Continuous planarWedgeChart :=
  planeProductCoordinates.symm.continuous.comp (continuous_fst.prodMk (continuous_fst.mul continuous_snd))

lemma slopeScalarTest_support_coordinates {χ ψ : ℝ → ℝ}
    (hχ0 : 0 ∉ tsupport χ) {y : Plane} (hy : y ∈ tsupport (slopeScalarTest χ ψ)) :
    (planeProductCoordinates y).1 ∈ tsupport χ ∧
      (planeProductCoordinates y).2/(planeProductCoordinates y).1 ∈ tsupport ψ := by
  have hr : (planeProductCoordinates y).1 ∈ tsupport χ := by
    by_contra hh
    have heχ := notMem_tsupport_iff_eventuallyEq.mp hh
    have he : slopeScalarTest χ ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [(planeProductCoordinates.continuous.fst.tendsto y).eventually heχ] with z hz
      simp only [slopeScalarTest,hz,Pi.zero_apply,zero_mul]
    exact notMem_tsupport_iff_eventuallyEq.mpr he hy
  refine ⟨hr,?_⟩
  have hr0 : (planeProductCoordinates y).1≠0 := fun hh ↦ hχ0 (hh ▸ hr)
  by_contra hh
  have heψ := notMem_tsupport_iff_eventuallyEq.mp hh
  have hc : ContinuousAt (fun z : Plane ↦ (planeProductCoordinates z).2/(planeProductCoordinates z).1) y :=
    planeProductCoordinates.continuous.snd.continuousAt.div planeProductCoordinates.continuous.fst.continuousAt hr0
  have he : slopeScalarTest χ ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hc.eventually heψ] with z hz
    simp only [slopeScalarTest,hz,Pi.zero_apply,mul_zero]
  exact notMem_tsupport_iff_eventuallyEq.mpr he hy

lemma planarWedgeChart_coordinates_inverse {y : Plane} (hy : (planeProductCoordinates y).1≠0) :
    planarWedgeChart ((planeProductCoordinates y).1,
      (planeProductCoordinates y).2/(planeProductCoordinates y).1)=y := by
  simp only [planarWedgeChart,mul_div_cancel₀ _ hy]
  exact ContinuousLinearEquiv.symm_apply_apply planeProductCoordinates y

lemma slopeScalarTest_compactSupport {χ ψ : ℝ → ℝ} (hχ0 : 0 ∉ tsupport χ)
    (hχ : HasCompactSupport χ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (slopeScalarTest χ ψ) := by
  apply ((hχ.prod hψ).image planarWedgeChart_continuous).of_isClosed_subset isClosed_closure
  intro y hy
  obtain ⟨hr,hs⟩ := slopeScalarTest_support_coordinates hχ0 hy
  exact ⟨((planeProductCoordinates y).1,(planeProductCoordinates y).2/(planeProductCoordinates y).1),
    ⟨hr,hs⟩,planarWedgeChart_coordinates_inverse (fun hh ↦ hχ0 (hh ▸ hr))⟩

lemma slopeScalarTest_derivative_zero {χ ψ : ℝ → ℝ} {y : Plane}
    (hy : (planeProductCoordinates y).1 ∉ tsupport χ ∨
      (planeProductCoordinates y).2/(planeProductCoordinates y).1 ∉ tsupport ψ)
    (hχ0 : 0 ∉ tsupport χ) : fderiv ℝ (slopeScalarTest χ ψ) y=0 := by
  apply fderiv_of_notMem_tsupport
  intro hh
  obtain ⟨hr,hs⟩ := slopeScalarTest_support_coordinates hχ0 hh
  exact hy.elim (fun h ↦ h hr) (fun h ↦ h hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_norm_sq_coordinates (v : Plane) :
    ‖v‖^2=(planeProductCoordinates v).1^2+(planeProductCoordinates v).2^2 := by
  rw [← real_inner_self_eq_norm_sq,plane_inner_coordinates]
  ring

lemma exists_smooth_radial_test {a b : ℝ} (hab : a<b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo a b ∧ (∫ r : ℝ, χ r)=1 := by
  let φ : ContDiffBump ((a+b)/2) :=
    ⟨(b-a)/8,(b-a)/4,by linarith,by linarith⟩
  refine ⟨φ.normed volume,φ.contDiff_normed,φ.hasCompactSupport_normed,?_,φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  intro r hr
  simp only [Metric.mem_closedBall,Real.dist_eq,abs_le] at hr
  change -( (b-a)/4) ≤ r-(a+b)/2 ∧ r-(a+b)/2 ≤ (b-a)/4 at hr
  constructor <;> linarith

lemma minimalGraphDensity_slope {g : Plane → ℝ} {χ ψ f q : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) {r s : ℝ} (hr : r≠0)
    (hg : planeProductCoordinates (gradient g (planarWedgeChart (r,s)))=(f s-s*q s,q s)) :
    minimalGraphDensity g (slopeScalarTest χ ψ) (planarWedgeChart (r,s)) =
      deriv χ r*((f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s)+
        (χ r/r)*(coneSlopeFlux f q s*deriv ψ s) := by
  rw [minimalGraphDensity,slopeScalarTest_derivative hχ hψ hχ0 hr,
    plane_norm_sq_coordinates,hg]
  dsimp only [Prod.fst,Prod.snd,coneSlopeReciprocalArea,coneSlopeFlux]
  ring_nf

theorem stationary_euler_graph_affine {g : Plane → ℝ} {a b c d : ℝ}
    (ha : 0<a) (hab : a<b)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (hC : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, ContinuousAt (fderiv ℝ g) (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      tsupport Ψ ⊆ planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {r₀ r x s : ℝ} (hr₀ : r₀ ∈ Ioo a b) (hr : r ∈ Ioo a b)
    (hx : x ∈ Ioo c d) (hs : s ∈ Ioo c d) :
    g (planarWedgeChart (r,s)) =
      r*(g (planarWedgeChart (r₀,x))/r₀+
        fderiv ℝ g (planarWedgeChart (r₀,x)) slopeVerticalVector*(s-x)) := by
  let f : ℝ → ℝ := fun t ↦ g (planarWedgeChart (r₀,t))/r₀
  let q : ℝ → ℝ := fun t ↦ fderiv ℝ g (planarWedgeChart (r₀,t)) slopeVerticalVector
  have hrd : r₀≠0 := (ha.trans hr₀.1).ne'
  have hfd (t : ℝ) (ht : t ∈ Ioo c d) : HasDerivAt f (q t) t :=
    graph_angular_slice_hasDerivAt hrd (hg r₀ hr₀ t ht)
  have hqc (t : ℝ) (ht : t ∈ Ioo c d) : ContinuousAt q t := by
    have hc : ContinuousAt (fun t : ℝ ↦ fderiv ℝ g (planarWedgeChart (r₀,t))) t :=
      (hC r₀ hr₀ t ht).comp (f := fun t : ℝ ↦ planarWedgeChart (r₀,t))
        (planarWedgeChart_hasDerivAt_angular r₀ t).continuousAt
    exact hc.clm_apply continuousAt_const
  have hfc : ContinuousOn f (Ioo c d) := fun t ht ↦ (hfd t ht).continuousAt.continuousWithinAt
  have hqC : ContinuousOn q (Ioo c d) := fun t ht ↦ (hqc t ht).continuousWithinAt
  have hcc := coneSlopeReciprocalArea_continuousOn hfc hqC
  have hu := hfc.sub (continuousOn_id.mul hqC)
  have hflux : ContinuousOn (coneSlopeFlux f q) (Ioo c d) :=
    (hqC.sub (continuousOn_id.mul hu)).mul hcc
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo c d →
      (∫ t : ℝ, coneSlopeFlux f q t*deriv ψ t)=
        (∫ t : ℝ, (f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t) := by
    intro ψ hψ hsψ
    obtain ⟨χ,hχ,hχc,hχs,hχi⟩ := exists_smooth_radial_test hab
    have hχpos : tsupport χ ⊆ Ioi (0 : ℝ) := fun t ht ↦ ha.trans (hχs ht).1
    have hχ0 : (0 : ℝ) ∉ tsupport χ := fun hh ↦ (lt_irrefl (0 : ℝ)) (hχpos hh)
    have hψc : HasCompactSupport ψ :=
      isCompact_Icc.of_isClosed_subset isClosed_closure (hsψ.trans Ioo_subset_Icc_self)
    let Ψ := slopeScalarTest χ ψ
    have hΨ := slopeScalarTest_contDiff hχ hψ hχ0
    have hΨc := slopeScalarTest_compactSupport hχ0 hχc hψc
    have hΨs : tsupport Ψ ⊆ planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) := by
      intro y hy
      obtain ⟨hr,ht⟩ := slopeScalarTest_support_coordinates hχ0 hy
      exact ⟨((planeProductCoordinates y).1,(planeProductCoordinates y).2/(planeProductCoordinates y).1),
        ⟨hχs hr,hsψ ht⟩,planarWedgeChart_coordinates_inverse (fun hh ↦ hχ0 (hh ▸ hr))⟩
    have hGi : Integrable (minimalGraphDensity g Ψ) := by
      apply minimalGraphDensity_integrable hΨ hΨc
      intro y hy
      obtain ⟨⟨r,t⟩,⟨hr,ht⟩,rfl⟩ := hΨs hy
      exact hC r hr t ht
    have hAi : Integrable (fun t ↦ (f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t) := by
      apply integrable_mul_on_tsupport hψ.continuous hψc
      intro t ht
      exact (hu.mul hcc).continuousAt (isOpen_Ioo.mem_nhds (hsψ ht))
    have hBi : Integrable (fun t ↦ coneSlopeFlux f q t*deriv ψ t) := by
      apply integrable_mul_on_tsupport (hψ.continuous_deriv (by simp)) hψc.deriv
      intro t ht
      exact hflux.continuousAt (isOpen_Ioo.mem_nhds (hsψ (tsupport_deriv_subset ht)))
    have hzero (r : ℝ) (hr : r≤0) (y : ℝ) :
        minimalGraphDensity g Ψ (planeProductCoordinates.symm (r,y))=0 := by
      have hz : r ∉ tsupport χ := fun hh ↦ not_lt_of_ge hr (hχpos hh)
      have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
        (y := planeProductCoordinates.symm (r,y)) (Or.inl (by simpa using hz)) hχ0
      simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div]
    have hid (r : ℝ) (hr : 0 < r) (t : ℝ) :
        minimalGraphDensity g Ψ (planarWedgeChart (r,t)) =
          deriv χ r*((f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t)+
            (χ r/r)*(coneSlopeFlux f q t*deriv ψ t) := by
      by_cases hrχ : r ∈ tsupport χ
      · by_cases htψ : t ∈ tsupport ψ
        · exact minimalGraphDensity_slope hχ hψ hχ0 hr.ne'
            (euler_graph_gradient ha hg he (hχs hrχ) hr₀ (hsψ htψ))
        · have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
            (y := planarWedgeChart (r,t)) (Or.inr (by simpa [planarWedgeChart,hr.ne'] using htψ)) hχ0
          simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div,
            image_eq_zero_of_notMem_tsupport htψ,deriv_of_notMem_tsupport htψ,mul_zero,add_zero]
      · have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
          (y := planarWedgeChart (r,t)) (Or.inl (by simpa [planarWedgeChart] using hrχ)) hχ0
        simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div,
          image_eq_zero_of_notMem_tsupport hrχ,deriv_of_notMem_tsupport hrχ,zero_mul,zero_div,add_zero]
    have hi := integral_slope_separated hGi hχ hχc hχpos hAi hBi hzero hid
    rw [hw Ψ hΨ hΨs,hχi,one_mul] at hi
    linarith
  have haf := (weak_cone_slope_affine hfd hqC hweak hx hs).2
  have hh := euler_graph_homogeneous ha hg he hr hr₀ hs
  change g (planarWedgeChart (r,s))/r=f s at hh
  rw [haf] at hh
  apply (div_eq_iff (ha.trans hr.1).ne').mp at hh
  simpa only [f,q,mul_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphReparam_fderiv (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) (y : Plane) :
    fderiv ℝ (graphReparam R v c g) y =
      (fderiv ℝ g (R y-v)).comp R.toContinuousLinearEquiv.toContinuousLinearMap := by
  change fderiv ℝ (fun z ↦ g (R z-v)+c) y = _
  rw [fderiv_add_const]
  have he := R.toContinuousLinearEquiv.comp_right_fderiv (f := fun z ↦ g (z-v)) (x := y)
  simp only [Function.comp_def,sub_eq_add_neg,fderiv_comp_add_right] at he ⊢
  exact he

lemma graphReparam_gradient (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) (y : Plane) :
    gradient (graphReparam R v c g) y=R.symm (gradient g (R y-v)) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,graphReparam_fderiv,ContinuousLinearMap.comp_apply]
  rw [← R.inner_map_map, R.apply_symm_apply,inner_gradient_left]
  rfl

lemma minimalGraphDensity_reparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    (g ψ : Plane → ℝ) (y : Plane) :
    minimalGraphDensity (graphReparam R v c g) (graphReparam R v 0 ψ) y =
      minimalGraphDensity g ψ (R y-v) := by
  rw [minimalGraphDensity,graphReparam_fderiv,graphReparam_gradient,
    ContinuousLinearMap.comp_apply]
  change fderiv ℝ ψ (R y-v) (R (R.symm (gradient g (R y-v)))) / _ = _
  rw [R.apply_symm_apply,R.symm.norm_map]
  rfl

lemma integral_minimalGraphDensity_reparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    (g ψ : Plane → ℝ) :
    (∫ y : Plane, minimalGraphDensity (graphReparam R v c g) (graphReparam R v 0 ψ) y) =
      ∫ y : Plane, minimalGraphDensity g ψ y := by
  simp_rw [minimalGraphDensity_reparam]
  calc
    _ = ∫ y : Plane, minimalGraphDensity g ψ (y-v) :=
      R.measurePreserving.integral_comp R.toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := integral_sub_right_eq_self _ _

lemma graphReparam_contDiffAt (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    {g : Plane → ℝ} {y : Plane} (hg : ContDiffAt ℝ 1 g (R y-v)) :
    ContDiffAt ℝ 1 (graphReparam R v c g) y := by
  exact (hg.comp y (R.toContinuousLinearEquiv.contDiff.contDiffAt.sub contDiffAt_const)).add contDiffAt_const

lemma graphReparam_contDiff (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphReparam R v c g) :=
  (hg.comp (R.toContinuousLinearEquiv.contDiff.sub contDiff_const)).add contDiff_const

lemma graphReparam_zero_tsupport (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (g : Plane → ℝ) :
    tsupport (graphReparam R v 0 g) = (fun y ↦ R y-v) ⁻¹' tsupport g := by
  have he : graphReparam R v 0 g = g ∘ (R.toHomeomorph.trans (Homeomorph.subRight v)) := by
    ext y
    simp [graphReparam]
  rw [he,tsupport_comp_eq_preimage]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positive_wedge_rectangle {U : Set Plane} (hU : IsOpen U) {z : Plane}
    (hz : z ∈ U) (hzp : 0<(planeProductCoordinates z).1) :
    ∃ a b c d : ℝ, 0<a ∧
      (planeProductCoordinates z).1 ∈ Ioo a b ∧
      (planeProductCoordinates z).2/(planeProductCoordinates z).1 ∈ Ioo c d ∧
      planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) ⊆ U := by
  let r := (planeProductCoordinates z).1
  let s := (planeProductCoordinates z).2/r
  have hW : planarWedgeChart (r,s)=z := planarWedgeChart_coordinates_inverse hzp.ne'
  have hu : planarWedgeChart ⁻¹' U ∈ 𝓝 (r,s) := by
    apply (hU.preimage planarWedgeChart_continuous).mem_nhds
    simpa only [mem_preimage,hW] using hz
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hu
  obtain ⟨a,b,hrab,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c,d,hscd,hcd⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  refine ⟨max a (r/2),b,c,d,lt_max_of_lt_right (by dsimp [r]; linarith),
    ⟨max_lt hrab.1 (by dsimp [r]; linarith),hrab.2⟩,hscd,?_⟩
  rintro _ ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
  exact hAB ⟨hab ⟨(le_max_left _ _).trans_lt hu.1,hu.2⟩,hcd ht⟩

theorem local_euler_graph_linear {U : Set Plane} (hU : IsOpen U) {g : Plane → ℝ}
    (hg : ∀ y ∈ U, ContDiffAt ℝ 1 g y)
    (he : ∀ y ∈ U, fderiv ℝ g y y=g y)
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ U →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {z : Plane} (hz : z ∈ U) (hzp : 0<(planeProductCoordinates z).1) :
    ∀ᶠ y in 𝓝 z, g y=fderiv ℝ g z y := by
  obtain ⟨a,b,c,d,ha,hr,hs,hW⟩ := positive_wedge_rectangle hU hz hzp
  let r := (planeProductCoordinates z).1
  let s := (planeProductCoordinates z).2/r
  have hWz : planarWedgeChart (r,s)=z := planarWedgeChart_coordinates_inverse hzp.ne'
  have hmem (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :
      planarWedgeChart (u,t) ∈ U := hW ⟨(u,t),⟨hu,ht⟩,rfl⟩
  have hgd (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :=
    (hg _ (hmem u hu t ht)).differentiableAt (by norm_num)
  have hgc (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :=
    (hg _ (hmem u hu t ht)).continuousAt_fderiv (by norm_num)
  have helin : g z/r=fderiv ℝ g z slopeHorizontalVector+s*fderiv ℝ g z slopeVerticalVector := by
    have hlin := congrArg (fderiv ℝ g z) (planarWedgeChart_expand r s)
    rw [hWz,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,he z hz] at hlin
    apply (div_eq_iff hzp.ne').mpr
    linarith
  have hc : ContinuousAt (fun y : Plane ↦ ((planeProductCoordinates y).1,
      (planeProductCoordinates y).2/(planeProductCoordinates y).1)) z :=
    planeProductCoordinates.continuous.fst.continuousAt.prodMk
      (planeProductCoordinates.continuous.snd.continuousAt.div
        planeProductCoordinates.continuous.fst.continuousAt hzp.ne')
  have hneigh := hc.eventually ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hr,hs⟩)
  filter_upwards [hneigh] with y hy
  let u := (planeProductCoordinates y).1
  let t := (planeProductCoordinates y).2/u
  have huy : planarWedgeChart (u,t)=y := planarWedgeChart_coordinates_inverse (ha.trans hy.1.1).ne'
  have hh := stationary_euler_graph_affine ha (hr.1.trans hr.2) hgd hgc
    (fun u hu t ht ↦ he _ (hmem u hu t ht))
    (fun Ψ hΨ hsΨ ↦ hw Ψ hΨ (hsΨ.trans hW)) hr hy.1 hs hy.2
  rw [hWz,huy,helin] at hh
  rw [hh]
  have hlin := congrArg (fderiv ℝ g z) (planarWedgeChart_expand u t)
  rw [huy,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hlin
  rw [hlin]
  ring

theorem local_euler_graph_linear_of_ne_zero {U : Set Plane} (hU : IsOpen U) {g : Plane → ℝ}
    (hg : ∀ y ∈ U, ContDiffAt ℝ 1 g y)
    (he : ∀ y ∈ U, fderiv ℝ g y y=g y)
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ U →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {z : Plane} (hz : z ∈ U) (hz0 : z≠0) :
    ∀ᶠ y in 𝓝 z, g y=fderiv ℝ g z y := by
  let n : Plane := ‖z‖⁻¹ • z
  have hzn : 0<‖z‖ := norm_pos_iff.mpr hz0
  have hn : ‖n‖=1 := by
    dsimp only [n]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hzn.le),inv_mul_cancel₀ hzn.ne']
  let R := planarNormalRotation n
  let H := graphReparam R 0 0 g
  have hH (y : Plane) : H y=g (R y) := by simp [H,graphReparam]
  have hHp : ∀ y ∈ R ⁻¹' U, ContDiffAt ℝ 1 H y := by
    intro y hy
    apply graphReparam_contDiffAt
    simpa only [sub_zero] using hg (R y) hy
  have hHe : ∀ y ∈ R ⁻¹' U, fderiv ℝ H y y=H y := by
    intro y hy
    rw [graphReparam_fderiv]
    change fderiv ℝ g (R y-0) (R y)=H y
    simpa only [sub_zero,hH] using he (R y) hy
  have hHw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ R ⁻¹' U →
      (∫ y : Plane, minimalGraphDensity H Ψ y)=0 := by
    intro Ψ hΨ hsΨ
    let ψ := graphReparam R.symm 0 0 Ψ
    have hψ := graphReparam_contDiff R.symm 0 0 hΨ
    have hsψ : tsupport ψ ⊆ U := by
      rw [graphReparam_zero_tsupport]
      intro y hy
      have hh := hsΨ hy
      simpa only [mem_preimage,sub_zero,R.apply_symm_apply] using hh
    have hrev : graphReparam R 0 0 ψ=Ψ := by
      ext y
      simp only [graphReparam,sub_zero,add_zero,R.symm_apply_apply,ψ]
    rw [← hrev,integral_minimalGraphDensity_reparam]
    exact hw ψ hψ hsψ
  have hzR : R.symm z ∈ R ⁻¹' U := by simpa using hz
  have hpR : 0<(planeProductCoordinates (R.symm z)).1 := by
    change 0<(planarWedgeCoordinates ((planarNormalRotation n).symm z)).1
    rw [planarNormalRotation_radial hn]
    dsimp only [n]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    positivity
  have hlocal := local_euler_graph_linear (hU.preimage R.continuous) hHp hHe hHw hzR hpR
  have hi := R.symm.continuous.continuousAt.eventually hlocal
  filter_upwards [hi] with y hy
  rw [hH,R.apply_symm_apply,graphReparam_fderiv] at hy
  change g y=fderiv ℝ g (R (R.symm z)-0) (R (R.symm y)) at hy
  simpa only [R.apply_symm_apply,sub_zero] using hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

lemma normalGraph_coordinates_eq_iff {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n g (normalPlaneCoordinates n x)=x ↔ g (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  constructor
  · intro hh
    simpa only [normalGraph_inner hn] using congrArg (fun v : Cover ↦ ⟪n,v⟫) hh
  · intro hh
    rw [normalGraph,hh,normalPlaneCoordinates_reconstruct hn x]

lemma rebasedGraph_apply (a n : Cover) (g : Plane → ℝ) (y : Plane) :
    rebasedGraph a n g y=g (y-normalPlaneCoordinates n a)+⟪n,a⟫ := rfl

lemma rebasedGraph_fderiv (a n : Cover) (g : Plane → ℝ) (y : Plane) :
    fderiv ℝ (rebasedGraph a n g) y=fderiv ℝ g (y-normalPlaneCoordinates n a) := by
  rw [rebasedGraph,graphReparam_fderiv]
  ext z
  rfl

lemma normalGraph_rebased (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    normalGraph n (rebasedGraph a n g) y=a+normalGraph n g (y-normalPlaneCoordinates n a) := by
  have ha := normalPlaneCoordinates_reconstruct hn a
  simp only [normalGraph,rebasedGraph_apply,add_smul]
  change normalPlaneLinearIsometry n y+(g (y-normalPlaneCoordinates n a) • n+⟪n,a⟫ • n)=
    a+(normalPlaneLinearIsometry n (y-normalPlaneCoordinates n a)+g (y-normalPlaneCoordinates n a) • n)
  rw [map_sub]
  change normalPlaneLinearIsometry n (normalPlaneCoordinates n a)+⟪n,a⟫ • n=a at ha
  rw [show normalPlaneLinearIsometry n (normalPlaneCoordinates n a)=a-⟪n,a⟫ • n from
    eq_sub_iff_add_eq.mpr ha]
  abel

lemma rebasedGraph_graph_eq (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n (rebasedGraph a n g) (normalPlaneCoordinates n x)=x ↔
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
  rw [normalGraph_rebased a hn,map_sub,eq_sub_iff_add_eq]
  constructor <;> intro hh <;> simpa only [add_comm] using hh

lemma rebasedGraph_continuous (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    Continuous (rebasedGraph a n g) :=
  (hg.comp (continuous_id.sub continuous_const)).add continuous_const

lemma rebasedGraph_weak_equation (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ)
    {p : Cover} {ρ : ℝ} (hρ : 0<ρ)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0)
    {Ψ : Plane → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hs : ∀ y ∈ tsupport Ψ, normalGraph n (rebasedGraph a n g) y ∈ Metric.ball p (ρ/2)) :
    (∫ y : Plane, minimalGraphDensity (rebasedGraph a n g) Ψ y)=0 := by
  let v := normalPlaneCoordinates n a
  let R := LinearIsometryEquiv.refl ℝ Plane
  let ψ := graphReparam R (-v) 0 Ψ
  have hψ := graphReparam_contDiff R (-v) 0 hΨ
  have hsψ (y : Plane) (hy : y ∈ tsupport ψ) : a+normalGraph n g y ∈ Metric.ball p (ρ/2) := by
    rw [graphReparam_zero_tsupport] at hy
    change y-(-v) ∈ tsupport Ψ at hy
    have hh := hs (y+v) (by simpa only [sub_neg_eq_add] using hy)
    rw [normalGraph_rebased a hn] at hh
    simpa only [v,add_sub_cancel_right] using hh
  have hi := stationary_graph_weak_equation a hn g hρ hstat hψ hsψ
  simp_rw [graphAreaVector_norm_sqrt hn] at hi
  have hh : graphReparam R v 0 ψ=Ψ := by
    ext y
    simp [graphReparam,ψ,R]
  rw [← hh]
  change (∫ y : Plane, minimalGraphDensity (graphReparam R v ⟪n,a⟫ g) (graphReparam R v 0 ψ) y)=0
  rw [integral_minimalGraphDensity_reparam]
  exact hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem conical_stationary_patch_plane {A : Set Cover}
    (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {a n p : Cover} {g : Plane → ℝ} {R ρ : ℝ}
    (hn : ‖n‖=1) (hg : LipschitzWith (1/4) g) (hρ : 0<ρ)
    (hC : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y)
    (hRp : p ∈ Metric.ball a R)
    (hp : p ∈ coverEssentialBoundary A) (hpn : ‖p‖<1) (hp0 : p≠0)
    (hgraph : ∀ x ∈ Metric.closedBall p (2*ρ), x ∈ coverEssentialBoundary A ↔
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0) :
    ∃ N : Cover, ‖N‖=1 ∧ ∀ᶠ x in 𝓝 p, x ∈ coverEssentialBoundary A ↔ ⟪N,x⟫=0 := by
  let H := rebasedGraph a n g
  let v := normalPlaneCoordinates n a
  let G := normalGraph n H
  have hHc : Continuous H := rebasedGraph_continuous a n hg.continuous
  have hGc : Continuous G :=
    (normalPlaneLinearIsometry n).continuous.add (hHc.smul continuous_const)
  let U : Set Plane := (fun y ↦ y-v) ⁻¹' Metric.ball (0 : Plane) R ∩
    G ⁻¹' (Metric.ball p (ρ/2) ∩ Metric.ball (0 : Cover) 1)
  have hU : IsOpen U :=
    (Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)).inter
      ((Metric.isOpen_ball.inter Metric.isOpen_ball).preimage hGc)
  have hHC (y : Plane) (hy : y ∈ U) : ContDiffAt ℝ 1 H y := by
    apply graphReparam_contDiffAt
    exact hC _ (Metric.ball_subset_closedBall hy.1)
  have hbigger (x : Cover) (hx : x ∈ Metric.ball p (ρ/2)) : x ∈ Metric.ball p (2*ρ) :=
    Metric.ball_subset_ball (by linarith) hx
  have hxp (y : Plane) : normalPlaneCoordinates n (G y)=y := normalPlaneCoordinates_graph hn H y
  have hEuler (y : Plane) (hy : y ∈ U) : fderiv ℝ H y y=H y := by
    have hxb := hy.2.1
    have hxgraph : normalGraph n g (normalPlaneCoordinates n (G y-a))=G y-a := by
      apply (rebasedGraph_graph_eq a hn g (G y)).mp
      rw [hxp]
    have hxB := (hgraph (G y) (Metric.ball_subset_closedBall (hbigger _ hxb))).mpr hxgraph
    have hproj : normalPlaneCoordinates n (G y-a)=y-v := by rw [map_sub,hxp]
    have hgd : DifferentiableAt ℝ g (normalPlaneCoordinates n (G y-a)) := by
      rw [hproj]
      exact (hC _ (Metric.ball_subset_closedBall hy.1)).differentiableAt (by norm_num)
    have hloc : ∀ᶠ x in 𝓝 (G y), x ∈ coverEssentialBoundary A →
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hbigger _ hxb)] with x hx
      exact (hgraph x (Metric.ball_subset_closedBall hx)).mp
    have hr := cone_graph_radial_derivative hcone hn hxB
      (by simpa only [Metric.mem_ball,dist_zero_right] using hy.2.2) hgd hloc
    rw [hproj,hxp] at hr
    rw [rebasedGraph_fderiv]
    exact hr.trans (normalGraph_inner hn H y)
  have hweak (Ψ : Plane → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hs : tsupport Ψ ⊆ U) :
      (∫ y : Plane, minimalGraphDensity H Ψ y)=0 :=
    rebasedGraph_weak_equation a hn g hρ hstat hΨ (fun y hy ↦ (hs hy).2.1)
  have hpclosed : p ∈ Metric.closedBall p (2*ρ) := Metric.mem_closedBall_self (by linarith)
  have hpG : G (normalPlaneCoordinates n p)=p :=
    (rebasedGraph_graph_eq a hn g p).mpr ((hgraph p hpclosed).mp hp)
  have hpU : normalPlaneCoordinates n p ∈ U := by
    refine ⟨?_,?_⟩
    · simp only [mem_preimage,v,← map_sub,Metric.mem_ball,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n (p-a)).trans_lt (by simpa only [Metric.mem_ball,dist_eq_norm] using hRp)
    · change G (normalPlaneCoordinates n p) ∈ Metric.ball p (ρ/2) ∩ Metric.ball (0 : Cover) 1
      rw [hpG]
      exact ⟨Metric.mem_ball_self (by positivity),by simpa using hpn⟩
  have hpz : normalPlaneCoordinates n p≠0 := by
    apply cone_graph_radial_projection_ne_zero hn hp0 (L := fderiv ℝ H (normalPlaneCoordinates n p))
    have he := hEuler _ hpU
    have hpheight := congrArg (fun x : Cover ↦ ⟪n,x⟫) hpG
    rw [normalGraph_inner hn] at hpheight
    exact he.trans hpheight
  have hline := local_euler_graph_linear_of_ne_zero hU hHC hEuler hweak hpU hpz
  let M := n-normalPlaneEmbedding n (gradient H (normalPlaneCoordinates n p))
  have hM : 0<‖M‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1)
    (graphSlopeVector_norm_ge hn (gradient H (normalPlaneCoordinates n p)))
  let N := ‖M‖⁻¹ • M
  have hN : ‖N‖=1 := by
    dsimp only [N]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hM.le),inv_mul_cancel₀ hM.ne']
  refine ⟨N,hN,?_⟩
  have hprojline := (normalPlaneCoordinates n).continuous.continuousAt.eventually hline
  filter_upwards [hprojline,Metric.ball_mem_nhds p (by positivity : 0<2*ρ)] with x hx hxball
  rw [hgraph x (Metric.ball_subset_closedBall hxball),← rebasedGraph_graph_eq a hn g,
    normalGraph_coordinates_eq_iff hn]
  change H (normalPlaneCoordinates n x)=⟪n,x⟫ ↔ ⟪N,x⟫=0
  rw [hx]
  have hinner : ⟪N,x⟫=‖M‖⁻¹*(⟪n,x⟫-fderiv ℝ H (normalPlaneCoordinates n p) (normalPlaneCoordinates n x)) := by
    rw [show N=‖M‖⁻¹ • M from rfl,real_inner_smul_left]
    congr 1
    rw [show M=n-normalPlaneEmbedding n (gradient H (normalPlaneCoordinates n p)) from rfl,
      inner_sub_left,normalPlaneEmbedding_inner_coordinates hn,inner_gradient_left]
  rw [hinner,mul_eq_zero,inv_eq_zero,or_iff_right hM.ne',sub_eq_zero]
  exact eq_comm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverEssentialBoundary_isClosed (A : Set Cover) : IsClosed (coverEssentialBoundary A) := by
  rw [coverEssentialBoundary_eq_support]
  exact Measure.isClosed_support.inter Measure.isClosed_support

lemma inner_kernel_mono_of_local {n m x : Cover} (hx : ⟪n,x⟫=0)
    (hlocal : ∀ᶠ y in 𝓝 x, ⟪n,y⟫=0 → ⟪m,y⟫=0) :
    ∀ v : Cover, ⟪n,v⟫=0 → ⟪m,v⟫=0 := by
  intro v hv
  have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (show Continuous (fun t : ℝ ↦ x+t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
  have he : (fun t : ℝ ↦ ⟪m,x+t • v⟫) =ᶠ[𝓝 0] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [ht.eventually hlocal] with t h
    exact h (by simp only [inner_add_right,inner_smul_right,hx,hv,mul_zero,add_zero])
  have hd : HasDerivAt (fun t : ℝ ↦ ⟪m,x+t • v⟫) ⟪m,v⟫ 0 := by
    simpa only [inner_add_right,inner_smul_right,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const ⟪m,v⟫).const_add ⟪m,x⟫)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq he)

lemma inner_kernel_eq_of_local {n m x : Cover} (hx : ⟪n,x⟫=0)
    (hlocal : ∀ᶠ y in 𝓝 x, ⟪n,y⟫=0 ↔ ⟪m,y⟫=0) :
    ∀ v : Cover, ⟪n,v⟫=0 ↔ ⟪m,v⟫=0 := by
  have hmx := (hlocal.self_of_nhds).mp hx
  exact fun v ↦ ⟨inner_kernel_mono_of_local hx (hlocal.mono fun _ h ↦ h.mp) v,
    inner_kernel_mono_of_local hmx (hlocal.mono fun _ h ↦ h.mpr) v⟩

lemma normal_plane_disk_preconnected {n : Cover} (hn : ‖n‖=1) :
    IsPreconnected {x : Cover | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0} := by
  have he : normalPlaneEmbedding n '' (Metric.ball (0 : Plane) 1 \ {0}) =
      {x : Cover | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨normalPlaneEmbedding_inner hn z,?_,?_⟩
      · rw [normalPlaneEmbedding_norm]
        simpa only [Metric.mem_ball,dist_zero_right] using hz.1
      · intro hh
        have hhz := congrArg (normalPlaneCoordinates n) hh
        exact hz.2 (by simpa only [normalPlaneCoordinates_embedding,map_zero,mem_singleton_iff] using hhz)
    · rintro ⟨hx,hb,h0⟩
      have hh : normalPlaneEmbedding n (normalPlaneCoordinates n x)=x := by
        simpa only [hx,zero_smul,add_zero] using normalPlaneCoordinates_reconstruct hn x
      refine ⟨normalPlaneCoordinates n x,⟨?_,?_⟩,hh⟩
      · simp only [Metric.mem_ball,dist_zero_right]
        exact (normalPlaneCoordinates_norm_le n x).trans_lt hb
      · intro hz
        have hz' : normalPlaneCoordinates n x=0 := hz
        rw [hz'] at hh
        have he0 : normalPlaneEmbedding n (0 : Plane)=0 := (normalPlaneLinearIsometry n).map_zero
        exact h0 (hh.symm.trans he0)
  rw [← he]
  exact (planar_punctured_ball_preconnected (by norm_num : (0 : ℝ)<1)).image _
    (normalPlaneLinearIsometry n).continuous.continuousOn

theorem local_plane_disk_continuation {B : Set Cover} (hB : IsClosed B)
    (hloc : ∀ p ∈ B, ‖p‖<1 → p≠0 →
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0)
    {n p : Cover} (hn : ‖n‖=1) (hp : p∈B) (hpn : ‖p‖<1) (hp0 : p≠0)
    (hnloc : ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0) :
    ∀ q : Cover, ⟪n,q⟫=0 → ‖q‖<1 → q≠0 →
      ∀ᶠ x in 𝓝 q, x∈B ↔ ⟪n,x⟫=0 := by
  let D : Set Cover := {x | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0}
  let K : Set Cover := {q | ∀ᶠ x in 𝓝 q, x∈B ↔ ⟪n,x⟫=0}
  have hKo : IsOpen K := isOpen_setOfPred_eventually_nhds
  have hKc : IsClosed ((Subtype.val : D → Cover) ⁻¹' K) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    by_cases hqB : (q : Cover)∈B
    · obtain ⟨m,hm,hmloc⟩ := hloc q hqB q.prop.2.1 q.prop.2.2
      let U : Set Cover := {y | ∀ᶠ x in 𝓝 y, x∈B ↔ ⟪m,x⟫=0}
      have hUo : IsOpen U := isOpen_setOfPred_eventually_nhds
      have hqU : (q : Cover)∈U := hmloc
      apply Filter.mem_of_superset ((hUo.preimage continuous_subtype_val).mem_nhds hqU)
      intro z hz hzK
      have he : ∀ x : Cover, ⟪n,x⟫=0 ↔ ⟪m,x⟫=0 :=
        inner_kernel_eq_of_local z.prop.1 (hzK.and hz |>.mono fun _ h ↦ h.1.symm.trans h.2)
      apply hq
      change ∀ᶠ x in 𝓝 (q : Cover), x∈B ↔ ⟪n,x⟫=0
      exact hmloc.mono fun x h ↦ h.trans (he x).symm
    · apply Filter.mem_of_superset ((hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds hqB)
      intro z hz hzK
      exact hz ((hzK.self_of_nhds).mpr z.prop.1)
  have : PreconnectedSpace D :=
    isPreconnected_iff_preconnectedSpace.mp (normal_plane_disk_preconnected hn)
  have hpD : p∈D := ⟨(hnloc.self_of_nhds).mp hp,hpn,hp0⟩
  have he := (show IsClopen ((Subtype.val : D → Cover) ⁻¹' K) from
    ⟨hKc,hKo.preimage continuous_subtype_val⟩).eq_univ ⟨⟨p,hpD⟩,hnloc⟩
  intro q hqn hqb hq0
  have hh : (⟨q,hqn,hqb,hq0⟩ : D)∈(Subtype.val : D → Cover) ⁻¹' K := by rw [he]; trivial
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma two_cover_planes_meet {n m : Cover} (hn : ‖n‖=1) :
    ∃ q : Cover, ⟪n,q⟫=0 ∧ ⟪m,q⟫=0 ∧ ‖q‖<1 ∧ q≠0 := by
  let v := normalPlaneCoordinates n m
  have hw : ∃ w : Plane, w≠0 ∧ ⟪w,v⟫=0 := by
    by_cases hv : v=0
    · refine ⟨EuclideanSpace.single 0 1,?_,by simp [hv]⟩
      intro h
      have hh := congrArg (fun z : Plane ↦ z 0) h
      norm_num at hh
    · exact exists_planar_perpendicular hv
  obtain ⟨w,hw,hwi⟩ := hw
  let x := normalPlaneEmbedding n w
  have hx : 0<‖x‖ := by rw [normalPlaneEmbedding_norm]; exact norm_pos_iff.mpr hw
  have hnxi : ⟪n,x⟫=0 := normalPlaneEmbedding_inner hn w
  have hmxi : ⟪m,x⟫=0 := by
    rw [real_inner_comm]
    exact (normalPlaneEmbedding_inner_coordinates hn w m).trans hwi
  let q := ((1/2 : ℝ)*‖x‖⁻¹) • x
  have hqn : ‖q‖=(1/2 : ℝ) := by
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(1/2 : ℝ)*‖x‖⁻¹),
      mul_assoc,inv_mul_cancel₀ hx.ne',mul_one]
  refine ⟨q,?_,?_,by rw [hqn]; norm_num,?_⟩
  · simp only [q,inner_smul_right,hnxi,mul_zero]
  · simp only [q,inner_smul_right,hmxi,mul_zero]
  · intro hh
    rw [hh,norm_zero] at hqn
    norm_num at hqn

theorem closed_locally_planar_single_plane {B : Set Cover} (hB : IsClosed B)
    (hloc : ∀ p ∈ B, ‖p‖<1 → p≠0 →
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0)
    {p : Cover} (hp : p∈B) (hpn : ‖p‖<1) (hp0 : p≠0) :
    ∃ n : Cover, ‖n‖=1 ∧ ∀ x : Cover, ‖x‖<1 → x∈B → ⟪n,x⟫=0 := by
  obtain ⟨n,hn,hnloc⟩ := hloc p hp hpn hp0
  have hnext := local_plane_disk_continuation hB hloc hn hp hpn hp0 hnloc
  refine ⟨n,hn,?_⟩
  intro q hqb hqB
  by_cases hq0 : q=0
  · simp [hq0]
  obtain ⟨m,hm,hmloc⟩ := hloc q hqB hqb hq0
  have hmext := local_plane_disk_continuation hB hloc hm hqB hqb hq0 hmloc
  obtain ⟨z,hzn,hzm,hzb,hz0⟩ := two_cover_planes_meet (m := m) hn
  have hnz := hnext z hzn hzb hz0
  have hmz := hmext z hzm hzb hz0
  have he := inner_kernel_eq_of_local hzn (hnz.and hmz |>.mono fun _ h ↦ h.1.symm.trans h.2)
  exact (he q).mpr ((hmloc.self_of_nhds).mp hqB)

lemma cover_punctured_ball_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball (0 : Cover) r \ {0}) := by
  let f := OpenPartialHomeomorph.univBall (0 : Cover) r
  have hrank : 1 < Module.rank ℝ Cover := by
    rw [← Module.finrank_eq_rank]
    norm_num [Cover]
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : Cover)).isPreconnected
  have hi : f '' ({0}ᶜ : Set Cover) = Metric.ball (0 : Cover) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target (0 : Cover) hr]
        exact f.map_source (by simp [f])
      · intro he
        have he0 : f x=0 := he
        have hh := congrArg f.symm he0
        rw [f.left_inv (by simp [f]),OpenPartialHomeomorph.univBall_symm_apply_center] at hh
        exact hx hh
    · rintro ⟨hy,hy0⟩
      have hyt : y∈f.target := by rwa [OpenPartialHomeomorph.univBall_target _ hr]
      refine ⟨f.symm y,?_,f.right_inv hyt⟩
      intro hz
      have hz' : f.symm y=0 := hz
      have hh := congrArg f hz'
      rw [f.right_inv hyt,OpenPartialHomeomorph.univBall_apply_zero] at hh
      exact hy0 hh
  rw [← hi]
  exact hc.image f (OpenPartialHomeomorph.continuous_univBall (0 : Cover) r).continuousOn

lemma cover_boundary_nonzero {A : Set Cover} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 < r)
    (hpos : 0<volume (Metric.ball (0 : Cover) r ∩ A))
    (hneg : 0<volume (Metric.ball (0 : Cover) r ∩ Aᶜ)) :
    ∃ p : Cover, ‖p‖ < r ∧ p≠0 ∧ p∈coverEssentialBoundary A := by
  by_contra he
  have hd : Disjoint (Metric.ball (0 : Cover) r \ {0}) (coverEssentialBoundary A) := by
    rw [Set.disjoint_left]
    intro x hx hb
    exact he ⟨x,by simpa only [Metric.mem_ball,dist_zero_right] using hx.1,hx.2,hb⟩
  have hnull (B : Set Cover) (h : volume ((Metric.ball (0 : Cover) r \ {0}) ∩ B)=0) :
      volume (Metric.ball (0 : Cover) r ∩ B)=0 := by
    apply measure_mono_null (t := ((Metric.ball (0 : Cover) r \ {0}) ∩ B) ∪ {0}) ?_
      (measure_union_null h (measure_singleton 0))
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inr hx0
    · exact Or.inl ⟨⟨hx.1,hx0⟩,hx.2⟩
  rcases connected_cover_phase hA (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0))
    (cover_punctured_ball_preconnected hr) hd with hh|hh
  · exact (ne_of_gt hpos) (hnull A hh)
  · exact (ne_of_gt hneg) (hnull Aᶜ hh)

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem strict_C1_cone_halfspace_oai {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1})
    (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (hC : ∀ p : Cover, ‖p‖<1 → p≠0 → p∈coverEssentialBoundary A → CoverC1BoundaryAt A p)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (h0 : (0 : Cover)∈coverEssentialBoundary A) :
    ∃ n : Cover, ‖n‖=1 ∧ ∀ᵐ x ∂(volume : Measure Cover), x∈Metric.ball (0 : Cover) 1 →
      (x∈A ↔ 0<⟪n,x⟫) := by
  have hposneg := h0 1 (by norm_num)
  have hpos : 0<volume (Metric.ball (0 : Cover) 1 ∩ A) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hposneg.1).1
  have hneg : 0<volume (Metric.ball (0 : Cover) 1 ∩ Aᶜ) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hposneg.2).1
  obtain ⟨p,hpn,hp0,hp⟩ := cover_boundary_nonzero hA (by norm_num : (0 : ℝ)<1) hpos hneg
  have hloc (q : Cover) (hq : q∈coverEssentialBoundary A) (hqn : ‖q‖<1) (hq0 : q≠0) :
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 q, x∈coverEssentialBoundary A ↔ ⟪n,x⟫=0 := by
    obtain ⟨a,n,g,R,ρ,hn,hg,hR,hρ,hgC,hsub,hgraph,hstat⟩ :=
      strict_C1_patch_stationary hA heq hflux hq hqn (hC q hqn hq0 hq)
    have hqR := hsub (Metric.mem_closedBall_self (by positivity : 0≤2*ρ))
    exact conical_stationary_patch_plane hcone hn hg hρ hgC hqR hq hqn hq0 hgraph hstat
  obtain ⟨n,hn,hall⟩ := closed_locally_planar_single_plane (coverEssentialBoundary_isClosed A) hloc hp hpn hp0
  rcases cover_boundary_plane_phases hA hn
    (fun x hx hb ↦ hall x (by simpa only [Metric.mem_ball,dist_zero_right] using hx) hb) hpos hneg with h|h
  · exact ⟨n,hn,h⟩
  · refine ⟨-n,by simpa using hn,?_⟩
    simpa only [inner_neg_left,neg_pos] using h

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.strict_C1_cone_halfspace_oai := @OAI.CubicTorus.strict_C1_cone_halfspace_oai
