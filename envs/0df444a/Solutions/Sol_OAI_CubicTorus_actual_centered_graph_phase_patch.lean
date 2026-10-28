-- Prove2me | solution 1 for OAI.CubicTorus.actual_centered_graph_phase_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:09:52.0134+00:00
-- url     : https://prove2.me/submissions/a3482f19-c4d1-4e96-a8d4-7feeb4fc1e7d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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

lemma setIntegral_lift_measurable {f : Torus → ℝ} (hf : Measurable f)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f z ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f (quotientMap x) := by
  change (∫ z in E, f z ∂Measure.map quotientMap (volume.restrict fundamentalCube)) = _
  rw [setIntegral_map hE hf.aestronglyMeasurable measurable_quotientMap.aemeasurable,
    Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

lemma volumeSupport_eq_closure {E : Set Torus} (hE : IsOpen E) :
    volumeSupport E = closure E := by
  apply Subset.antisymm
  · exact Measure.support_restrict_subset.trans inter_subset_left
  · apply closure_minimal _ (isClosed_volumeSupport E)
    have hh := Measure.interior_inter_support (μ := torusVolume) (s := E)
    change E ⊆ (torusVolume.restrict E).support
    simpa only [hE.interior_eq, Measure.support_eq_univ, inter_univ] using hh

lemma isMinimizerAt_closure_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E) = volumeSupport E := by
  rw [← volumeSupport_eq_closure (isOpen_openRepresentative E)]
  exact volumeSupport_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)

lemma isMinimizerAt_frontier_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative E) = volumeSupport E ∩ volumeSupport Eᶜ := by
  rw [frontier, (isOpen_openRepresentative E).interior_eq,
    isMinimizerAt_closure_openRepresentative hV hE hmin]
  simp only [openRepresentative, sdiff_eq, compl_compl]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma norm_quotientMap_le (x : Cover) : ‖quotientMap x‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) QuotientAddGroup.norm_mk_le_norm 2

lemma quotientMap_shortestLift (x : Torus) : quotientMap (shortestLift x) = x := by
  simp only [shortestLift, quotientMap_sub, quotientMap_representative, add_sub_cancel_right]

lemma norm_shortestLift (x : Torus) : ‖shortestLift x‖ = ‖x‖ := by
  have hh := dist_representative_cubeCenter (x + quotientMap cubeCenter)
  simpa only [dist_eq_norm, add_sub_cancel_right, shortestLift] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma quotientMap_injective_open_closed_cell {x y : Cover}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (he : quotientMap x = quotientMap y) : x = y := by
  obtain ⟨n, hn⟩ := same_quotient_lattice he
  have hz (i : Fin 3) : n i = 0 := by
    have he' := congrArg (fun z : Cover ↦ z i) hn
    change x i = y i + (n i : ℝ) at he'
    have hlt : (n i : ℝ) < 1 := by linarith [(hx i).2, (hy i).1]
    have hgt : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).1, (hy i).2]
    have hlt' : n i < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n i := by exact_mod_cast hgt
    omega
  rw [show n = 0 from funext hz, latticeVector_zero, add_zero] at hn
  exact hn

lemma quotientMap_image_ball (a : Cover) (r : ℝ) :
    quotientMap '' Metric.ball a r = Metric.ball (quotientMap a) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist (quotientMap y) (quotientMap a) < r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  · intro hx
    refine ⟨shortestLift (x - quotientMap a) + a, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_shortestLift] using hx
    · rw [quotientMap_add, quotientMap_shortestLift, sub_add_cancel]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

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

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
attribute [-instance] _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma closedBall_interior {r : ℝ} (hr : r < 3/8) :
    Metric.closedBall (c : Cover) r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-(c : Cover)) i).trans
    (show ‖x-(c : Cover)‖ ≤ r from hx)
  change ‖x i-(c : Cover) i‖ ≤ r at hh
  rw [Real.norm_eq_abs,abs_le] at hh
  have hc := coords c i
  constructor <;> linarith

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVC1Patch
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma integral_ball_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.ball a (r*R), f x) =
      r^3 * ∫ y in Metric.ball (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.ball a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at h
  rw [h, ← integral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.ball a (r*R) ↔ x ∈ Metric.ball (0 : Cover) R := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  change (Metric.ball a (r*R)).indicator f (r • x+a) =
    (Metric.ball (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.ball (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma fundamentalCube_inter_ball_preimage (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    fundamentalCube ∩ quotientMap ⁻¹' Metric.ball (quotientMap c) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨hx,hq⟩
    rw [← quotientMap_image_ball c r] at hq
    obtain ⟨y,hy,he⟩ := hq
    have he' := quotientMap_injective_open_closed_cell
      (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩) (hc hy) he.symm
    rwa [he']
  · intro hx
    refine ⟨fun i ↦ ⟨(hc hx i).1.le,(hc hx i).2⟩,?_⟩
    rw [mem_preimage, ← quotientMap_image_ball c r]
    exact mem_image_of_mem _ hx

lemma integral_quotient_ball (f : Torus → ℝ) (hf : Measurable f)
    (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap c) r, f x ∂torusVolume) =
      ∫ x in Metric.ball c r, f (quotientMap x) := by
  rw [setIntegral_lift_measurable hf Metric.isOpen_ball.measurableSet,
    fundamentalCube_inter_ball_preimage c r hc]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma integral_blowupCharacteristic_ball {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap c) (r*R)) =
      r^3 * ∫ x in Metric.ball (0 : Cover) R, blowupCharacteristic E c r x := by
  rw [← setIntegral_characteristic hE _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball _ (measurable_characteristic hE) c _ hc,
    integral_ball_affine_scaling _ c hr R]
  rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma blowupCharacteristic_affine (E : Set Torus) (c p x : Cover) (r s : ℝ) :
    blowupCharacteristic E c r (p+s • x) =
      blowupCharacteristic E (c+r • p) (r*s) x := by
  simp [blowupCharacteristic,smul_add,mul_smul,add_assoc]

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_CoverEssentialBoundary
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma cover_integral_indicator_ball {A : Set Cover} (hA : MeasurableSet A) (x : Cover) (t : ℝ) :
    (∫ y in Metric.ball x t, A.indicator (fun _ ↦ (1:ℝ)) y) =
      volume.real (A ∩ Metric.ball x t) := by
  rw [integral_indicator hA,Measure.restrict_restrict hA,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ]
  rfl

lemma integral_blowupCharacteristic_ball_center {E : Set Torus} (hE : MeasurableSet E)
    (c p : Cover) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hc : Metric.ball (c+r • p) (r*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap (c+r • p)) (r*t)) =
      r^3 * ∫ x in Metric.ball p t, blowupCharacteristic E c r x := by
  have hh := integral_blowupCharacteristic_ball hE (c+r • p) hr t hc
  have he := integral_ball_affine_scaling (blowupCharacteristic E c r) p (by norm_num : (0:ℝ)<1) t
  have ha (y : Cover) : blowupCharacteristic E c r (p+y) =
      blowupCharacteristic E (c+r • p) r y := by
    simpa only [one_smul,mul_one] using blowupCharacteristic_affine E c p y r 1
  simp only [one_mul,one_pow,one_smul] at he
  simp_rw [ha] at he
  rw [he]
  exact hh

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma torusVolume_lift_ball {E : Set Torus} (hE : MeasurableSet E)
    (x : Cover) (t : ℝ) (ht : Metric.ball x t ⊆ {y | ∀ i, 0<y i ∧ y i<1}) :
    torusVolume.real (E∩Metric.ball (quotientMap x) t)=
      volume.real ((quotientMap ⁻¹' E)∩Metric.ball x t) := by
  have hh := integral_blowupCharacteristic_ball_center hE (0 : Cover) x
    (by norm_num : (0 : ℝ)<1) t (by simpa only [one_smul,zero_add,one_mul] using ht)
  simp only [one_smul,zero_add,one_mul,one_pow] at hh
  rw [hh,← cover_integral_indicator_ball (hE.preimage measurable_quotientMap)]
  congr 1
  funext y
  classical
  by_cases hy : quotientMap y∈E <;>
    simp [blowupCharacteristic,characteristic,hy]

lemma coverEssentialBoundary_lift_iff {E : Set Torus} (hE : MeasurableSet E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈volumeSupport E ∩ volumeSupport Eᶜ := by
  have hO : IsOpen {y : Cover | ∀ i, 0<y i ∧ y i<1} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
        (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  have hs (t : ℝ) : Metric.ball x (min r t) ⊆ {y | ∀ i, 0<y i ∧ y i<1} :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hsub
  rw [mem_inter_iff,mem_volumeSupport_iff,mem_volumeSupport_iff]
  constructor
  · intro h
    constructor
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).1
      rw [← torusVolume_lift_ball hE x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).2
      rw [← preimage_compl,← torusVolume_lift_ball hE.compl x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
  · intro h t ht
    have h₁ := h.1 (min r t) (lt_min hr ht)
    have h₂ := h.2 (min r t) (lt_min hr ht)
    rw [torusVolume_lift_ball hE x (min r t) (hs t)] at h₁
    rw [torusVolume_lift_ball hE.compl x (min r t) (hs t),preimage_compl] at h₂
    have hmono (A : Set Cover) : volume.real (A∩Metric.ball x (min r t)) ≤
        volume.real (A∩Metric.ball x t) :=
      measureReal_mono (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _)))
    exact ⟨h₁.trans_le (hmono _),h₂.trans_le (hmono _)⟩

lemma isMinimizerAt_lifted_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈frontier (openRepresentative E) := by
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact coverEssentialBoundary_lift_iff hE hx

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem actual_centered_graph_phase_patch_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0 < r)
    (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (R ρ : ℝ) (U : Set Cover), R < r ∧
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
      U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
      (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
       (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))) := by
  let R := r/2
  let s := min (r/4) (1/8)
  have hR : 0<R := half_pos hr
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsR : s<R := by dsimp [s,R]; exact (min_le_left _ _).trans_lt (by linarith)
  have hcell : Metric.ball cubeCenter s ⊆ {x | ∀ i, 0<x i ∧ x i<1} := by
    let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
    apply Metric.ball_subset_closedBall.trans
    exact MovingCenter.closedBall_interior (c := c) (by
      have hh : s≤1/8 := min_le_right _ _
      linarith)
  have hb (x : Cover) (hx : x∈Metric.ball cubeCenter s) :
      quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter := by
    have hx' : x-cubeCenter∈Metric.ball (0 : Cover) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      have hh : ‖x-cubeCenter‖ < s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      have hsr : s < r := by dsimp [R] at hsR; linarith
      exact hh.trans hsr
    simpa only [add_sub_cancel] using hcover (x-cubeCenter) hx'
  have hlift (x : Cover) (hx : x∈Metric.ball cubeCenter s) :=
    isMinimizerAt_lifted_boundary hV hE hmin (hcell hx)
  have hp : cubeCenter∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    (hlift cubeCenter (Metric.mem_ball_self hs)).mpr hcenter
  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases
    (hE.preimage measurable_quotientMap) cubeCenter hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)) hp
    (fun x hx ha ↦ (hb x hx).mp ((hlift x hx).mp ha))
  obtain ⟨t,ht,htW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let ρ := t/3
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨R,ρ,W,by dsimp [R]; linarith,hn,hg,hg0,hR,hρ,?_,hW,?_,?_,hWU.trans hcell,
    fun x hx ↦ hb x (hWU hx),hphase.symm⟩
  · intro y hy
    apply hgC.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    apply Metric.closedBall_subset_ball _ hy
    dsimp [R]
    linarith
  · exact (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans htW
  · exact hWU.trans (Metric.ball_subset_ball hsR.le)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.actual_centered_graph_phase_patch_oai := @OAI.CubicTorus.actual_centered_graph_phase_patch_oai
