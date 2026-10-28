-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:01:19.841987+00:00
-- url     : https://prove2.me/submissions/700bf68d-5301-41c2-8157-5e4c3f3f48cd

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_CenteredJacobiChart_classical_ground_state
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_H1_translation_jacobi
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_center_normal_unique
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_centeredJacobiChart
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_reflection_weak_normal_sign

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

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

lemma admissible_translate {F : Cover → Cover} (hF : AdmissibleField F) (a : Cover) :
    AdmissibleField (fun x => F (x + a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const), ?_, fun x => hF.2.2 _⟩
  intro n x
  change F ((x + latticeVector n) + a) = F (x + a)
  rw [add_right_comm, hF.2.1]

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma flux_translation {F : Cover → Cover} (hF : AdmissibleField F)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) := by
    exact (by fun_prop : Measurable (fun z : Torus => z + quotientMap a)) hE
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hpre]
  have hG := admissible_translate hF (-a)
  have hG' : AdmissibleField (fun y => F (y - a)) := by simpa [sub_eq_add_neg] using hG
  rw [← setIntegral_lift (continuous_divergence hG'.1) (divergence_periodic hG'.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

end CubicTorus

namespace CubicTorus

lemma perimeter_translation_le {E : Set Torus} (hE : MeasurableSet E) (a : Cover) :
    perimeter ((fun z => z + quotientMap a) ⁻¹' E) ≤ perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_translation hF a hE]
  have hG : AdmissibleField (fun y => F (y - a)) := by
    simpa [sub_eq_add_neg] using admissible_translate hF (-a)
  exact le_iSup_of_le (fun y => F (y - a)) (le_iSup_of_le hG le_rfl)

lemma perimeter_translation_measurable {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective a
  refine le_antisymm (perimeter_translation_le hE b) ?_
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap b) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  have hh := perimeter_translation_le hpre (-b)
  have he : (fun z : Torus => z + quotientMap (-b)) ⁻¹'
      ((fun z : Torus => z + quotientMap b) ⁻¹' E) = E := by
    ext z
    simp [quotientMap_neg]
  rwa [he] at hh

theorem perimeter_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp, ← perimeter_congr_ae he]
  exact perimeter_translation_measurable (measurableSet_toMeasurable _ _) a

lemma volume_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    torusVolume ((fun z => z + a) ⁻¹' E) = torusVolume E :=
  (measurePreserving_add_right torusVolume a).measure_preimage hE

lemma finitePerimeter_translation {E : Set Torus} (hE : FinitePerimeter E) (a : Torus) :
    FinitePerimeter ((fun z => z + a) ⁻¹' E) := by
  refine ⟨hE.1.preimage (measurePreserving_add_right torusVolume a).quasiMeasurePreserving, ?_⟩
  rw [perimeter_translation hE.1]
  exact hE.2

theorem isMinimizerAt_translation {E : Set Torus} {V : ℝ} (hE : IsMinimizerAt V E) (a : Torus) :
    IsMinimizerAt V ((fun z => z + a) ⁻¹' E) := by
  refine ⟨finitePerimeter_translation hE.1 a, ?_, ?_⟩
  · rw [volume_translation hE.1.1, hE.2.1]
  · intro F hF hvF
    rw [perimeter_translation hE.1.1]
    exact hE.2.2 F hF hvF

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
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
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
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
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_eq_trace (F : Cover → Cover) (x : Cover) :
    divergence F x = LinearMap.trace ℝ Cover (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [divergence,Matrix.trace,LinearMap.toMatrix_apply]

lemma divergence_isometry_pullback (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : Differentiable ℝ F) (x : Cover) :
    divergence (fun y ↦ R.symm (F (R y))) x = divergence F (R x) := by
  rw [divergence_eq_trace,divergence_eq_trace]
  have hd := R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hF (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ R.symm (F (R y))) _ x at hd
  rw [hd.fderiv]
  have he : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap =
      R.symm.toLinearEquiv.conj (fderiv ℝ F (R x)).toLinearMap := rfl
  rw [he,LinearMap.trace_conj']

lemma isometry_pullback_contDiff (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ R.symm (F (R x))) :=
  R.symm.toContinuousLinearEquiv.contDiff.comp (hF.comp R.toContinuousLinearEquiv.contDiff)

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

lemma normalPlaneCoordinates_norm_le (n x : Cover) : ‖normalPlaneCoordinates n x‖ ≤ ‖x‖ := by
  simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using
    (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0

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

lemma volumeSupport_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    volumeSupport ((fun z ↦ z+b) ⁻¹' E) = (fun z ↦ z+b) ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : ((fun z ↦ z+b) ⁻¹' E) ∩ Metric.ball a r =
      (fun z ↦ z+b) ⁻¹' (E ∩ Metric.ball (a+b) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,dist_add_right]
  rw [he,Measure.real_def,Measure.real_def,
    volume_translation (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    openRepresentative ((fun z ↦ z+b) ⁻¹' E) =
      (fun z ↦ z+b) ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_translation hE.compl]
  rfl

lemma frontier_openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    frontier (openRepresentative ((fun z ↦ z+b) ⁻¹' E)) =
      (fun z ↦ z+b) ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_translation hE b]
  exact (Homeomorph.addRight b).preimage_frontier _ |>.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcWeight_le_two {p : Plane} (hp : ‖p‖≤1) : cmcWeight p≤2 := by
  have hh := cmcWeight_sq p
  nlinarith [sq_nonneg (cmcWeight p),norm_nonneg p]

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

lemma cmcJacobian_coercive {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/8)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  have hs := cmcWeight_pos p
  have hsq := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  have h8 : (cmcWeight p)^3≤8 := by
    have hh := cmcWeight_le_two hp
    nlinarith [sq_nonneg (cmcWeight p-2)]
  rw [cmcJacobian_self,le_div_iff₀ (by positivity : 0<(cmcWeight p)^3)]
  have hh := mul_le_mul_of_nonneg_right h8 (sq_nonneg ‖v‖)
  nlinarith [sq_nonneg ⟪p,v⟫]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
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

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

lemma cmcJacobian_symmetric (p v w : Plane) :
    ⟪v,cmcJacobian p w⟫=⟪cmcJacobian p v,w⟫ := by
  simp only [cmcJacobian_apply,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm v p]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
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

lemma plane_gradient_support {f : Plane → ℝ} : tsupport (gradient f)⊆tsupport f := by
  exact (tsupport_comp_subset (g := (InnerProductSpace.toDual ℝ Plane).symm) (by simp) _).trans
    (tsupport_fderiv_subset ℝ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_scalar_product {f η : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hf : ContinuousOn f S) (hη : Continuous η)
    (hs : tsupport η⊆S) : Continuous (fun y ↦ f y*η y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact ((hf y (hs hy)).continuousAt (hS.mem_nhds (hs hy))).mul hη.continuousAt
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_local_integration_by_parts {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) (v : Plane) :
    (∫ y, fderiv ℝ g y v*ψ y)= -(∫ y,g y*fderiv ℝ ψ y v) := by
  have hdf : ContinuousOn (fun y ↦ fderiv ℝ g y v) S :=
    (hgc.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun y ↦ fderiv ℝ g y v*ψ y) :=
    (continuous_local_scalar_product hS hdf hψ.continuous hs).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun y ↦ g y*fderiv ℝ ψ y v) :=
    (hg.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ g y*ψ y) :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun y hy ↦ ((hgc y (hs hy)).contDiffAt (hS.mem_nhds (hs hy))).differentiableAt (by simp))
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
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

lemma cmcCompress_symm (p u v : Plane) : ⟪cmcCompress p u,v⟫=⟪u,cmcCompress p v⟫ := by
  simp only [cmcCompress_apply,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,conj_trivial,real_inner_comm u p]
  ring

lemma cmcCompress_sq (p v : Plane) :
    cmcCompress p (cmcCompress p v)=cmcWeight p • cmcJacobian p v := by
  rw [cmcCompress_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,cmcJacobian_apply,smul_sub,smul_smul,smul_smul]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  rw [mul_inv_cancel₀ hw,one_smul,sub_sub]
  rw [← add_smul]
  congr 1
  congr 1
  rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
  field_simp
  ring

lemma cmcJacobian_compress (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • cmcCompress p (cmcCompress p v) := by
  rw [cmcCompress_sq,smul_smul,inv_mul_cancel₀ (cmcWeight_pos p).ne',one_smul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_HolderNear
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

lemma plane_decompose (v : Plane) : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+
    v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
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

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

lemma plane_divergence_integration_by_parts {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ y,planeDivergence F y*ψ y)= -(∫ y,fderiv ℝ ψ y (F y)) := by
  have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hi (i : Fin 2) : Integrable (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single i 1)) i*ψ y) :=
    (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous.comp
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hj (i : Fin 2) : Integrable (fun y ↦ F y i*fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    ((hcomp i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ _).mul_left
  have hpart (i : Fin 2) := C1_local_integration_by_parts isOpen_univ (hcomp i).continuous
    (hcomp i).contDiffOn hψ hc (subset_univ _) (EuclideanSpace.single i 1)
  simp_rw [plane_component_fderiv hF] at hpart
  have he (y : Plane) : fderiv ℝ ψ y (F y)=
      F y 0*fderiv ℝ ψ y (EuclideanSpace.single 0 1)+
      F y 1*fderiv ℝ ψ y (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose (F y)]
    simp
  simp_rw [planeDivergence,add_mul,he]
  rw [integral_add (hi 0) (hi 1),hpart 0,hpart 1,integral_add (hj 0) (hj 1)]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
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

lemma plane_gradient_mul {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ f y*g y) x=f x • gradient g x+g x • gradient f x := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right,inner_add_right,real_inner_smul_right,
    fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,starRingEnd_apply,star_trivial]

lemma plane_gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_components (u v : Plane) : ⟪u,v⟫=u 0*v 0+u 1*v 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,star_trivial]
  ring

lemma plane_gradient_component (f : Plane → ℝ) (y : Plane) (i : Fin 2) :
    gradient f y i=fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma planeDivergence_add {F G : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    planeDivergence (fun z ↦ F z+G z) y=planeDivergence F y+planeDivergence G y := by
  simp only [planeDivergence,fderiv_fun_add hF hG,add_apply,PiLp.add_apply]
  ring

lemma planeDivergence_smul {a : Plane → ℝ} {F : Plane → Plane} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hF : DifferentiableAt ℝ F y) :
    planeDivergence (fun z ↦ a z • F z) y=
      a y*planeDivergence F y+⟪gradient a y,F y⟫ := by
  rw [plane_inner_components]
  simp only [plane_gradient_component,planeDivergence,fderiv_fun_smul ha hF,
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_hessian_direction {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v : Plane) : fderiv ℝ (gradient g) y v=
      gradient (fun z ↦ fderiv ℝ g z v) y := by
  ext i
  rw [← plane_component_fderiv ((plane_gradient_contDiff hg).of_le (by simp))]
  simp_rw [plane_gradient_component]
  rw [fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v _

lemma plane_hessian_symmetric {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v w : Plane) : ⟪fderiv ℝ (gradient g) y v,w⟫=⟪v,fderiv ℝ (gradient g) y w⟫ := by
  rw [plane_hessian_direction hg,plane_hessian_direction hg]
  conv_rhs => rw [real_inner_comm]
  rw [inner_gradient_left,inner_gradient_left,fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
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

lemma planeDivergence_eq_trace (F : Plane → Plane) (y : Plane) :
    planeDivergence F y=planeTrace (fderiv ℝ F y) := by
  simp only [planeDivergence,planeTrace,Fin.sum_univ_two]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTrace_comp_comm (A B : Plane →L[ℝ] Plane) :
    planeTrace (A.comp B)=planeTrace (B.comp A) := by
  simp only [planeTrace,Fin.sum_univ_two,ContinuousLinearMap.comp_apply]
  rw [plane_decompose (B (EuclideanSpace.single 0 1)),
    plane_decompose (B (EuclideanSpace.single 1 1)),
    plane_decompose (A (EuclideanSpace.single 0 1)),
    plane_decompose (A (EuclideanSpace.single 1 1))]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma translateNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (a : Cover) (z : NormalBundle) :
    F (translateNormal a z).1=F ((z.1 : Cover)-a) := by
  change F (representative (quotientMap z.1-quotientMap a))=F ((z.1 : Cover)-a)
  rw [← quotientMap_sub]
  exact periodic_representative hp _

theorem isNormalMeasure_translation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (a : Cover) :
    IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) (μ.map (translateNormal a)) := by
  constructor
  · have hm : ((μ.map (translateNormal a)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_translateNormal a)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_translation_measurable hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (translateNormal a) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_translateNormal a).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_translation hF a hE]
    have hG : AdmissibleField (fun x ↦ F (x-a)) := by
      simpa only [sub_eq_add_neg] using admissible_translate hF (-a)
    rw [← hμ.2 _ hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪(z.2 : Cover),F (translateNormal a z).1⟫=⟪(z.2 : Cover),F ((z.1 : Cover)-a)⟫
      rw [translateNormal_periodic_eval hF.2.1]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
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

lemma surfaceJacobiB_add_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u+v) w=surfaceJacobiB μ q u w+surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_add,Prod.snd_add,map_add,inner_add_left]
  ring

lemma surfaceJacobiB_smul_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (c : ℝ) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (c • u) v=c*surfaceJacobiB μ q u v := by
  change ⟪c • u.2,v.2⟫-⟪surfaceMultiplier μ q (c • u.1),v.1⟫ =
    c*(⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫)
  simp only [map_smul,real_inner_smul_left]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponentScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (x : Cover) :
    (normalComponentScalar N hN hp i).val x=N x i := by
  simp only [normalComponentScalar,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
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

lemma directionalNormalScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v x : Cover) :
    (directionalNormalScalar N hN hp v).val x=⟪v,N x⟫ := by
  simp only [directionalNormalScalar,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,normalComponentScalar_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma surfaceJacobiB_sum_left {ι : Type*} (s : Finset ι)
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (u : ι → SurfaceJet μ) (w : SurfaceJet μ) :
    surfaceJacobiB μ q (∑ i∈s,u i) w=∑ i∈s,surfaceJacobiB μ q (u i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [surfaceJacobiB]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,surfaceJacobiB_add_left,ih]

lemma directionalNormalScalar_global_jacobi (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,
      surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) (v : Cover) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp v)) w=0 := by
  intro w hw
  simp only [directionalNormalScalar,map_sum,map_smul,surfaceJacobiB_sum_left,
    surfaceJacobiB_smul_left,hj _ w hw,mul_zero,Finset.sum_const_zero]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace LatticeIsometry

lemma measurePreserving (e : LatticeIsometry) : MeasurePreserving e.torus torusVolume torusVolume :=
  (e.addHom).measurePreserving e.torus.continuous e.torus.surjective rfl

lemma lattice (e : LatticeIsometry) (m : Fin 3 → ℤ) :
    ∃ n : Fin 3 → ℤ,e.cover (latticeVector m)=latticeVector n := by
  have he : quotientMap (e.cover (latticeVector m))=quotientMap (0 : Cover) := by
    rw [e.commute,quotientMap_latticeVector,e.map_zero]
    ext j; simp [quotientMap]
  obtain ⟨n,hn⟩ := same_quotient_lattice he
  exact ⟨n,by simpa only [zero_add] using hn⟩

lemma pullback_contDiff (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (e.pullback F) :=
  isometry_pullback_contDiff e.cover hF

lemma pullback_periodic (e : LatticeIsometry) {F : Cover → Cover}
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∀ m x,e.pullback F (x+latticeVector m)=e.pullback F x := by
  intro m x
  obtain ⟨n,hn⟩ := e.lattice m
  simp only [pullback,LinearIsometryEquiv.map_add,hn,hp]

lemma pullback_admissible (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (e.pullback F) := by
  refine ⟨e.pullback_contDiff hF.1,e.pullback_periodic hF.2.1,fun x ↦ ?_⟩
  simpa only [pullback,LinearIsometryEquiv.norm_map] using hF.2.2 (e.cover x)

lemma divergence_pullback (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (e.pullback F) x=divergence F (e.cover x) :=
  divergence_isometry_pullback e.cover (hF.differentiable (by simp)) x

lemma flux (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (e.torus ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence (e.symm.pullback F) x := by
  have hG := e.symm.pullback_admissible hF
  rw [←setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1)
    (hE.preimage e.torus.continuous.measurable),
    ←setIntegral_lift (continuous_divergence hG.1) (divergence_periodic hG.2.1) hE]
  have he : (fun z : Torus ↦ divergence F (representative z))=
      fun z ↦ divergence (e.symm.pullback F) (representative (e.torus z)) := by
    funext z
    rw [e.symm.divergence_pullback hF.1]
    have hq : quotientMap (e.cover.symm (representative (e.torus z)))=quotientMap (representative z) := by
      change quotientMap (e.symm.cover (representative (e.torus z)))=quotientMap (representative z)
      rw [e.symm.commute,quotientMap_representative,quotientMap_representative]
      exact e.torus.symm_apply_apply z
    obtain ⟨n,hn⟩ := same_quotient_lattice hq
    change divergence F (representative z)=divergence F (e.cover.symm (representative (e.torus z)))
    rw [hn,divergence_periodic hF.2.1]
  rw [he]
  exact e.measurePreserving.setIntegral_preimage_emb e.torus.toHomeomorph.measurableEmbedding
    (fun z ↦ divergence (e.symm.pullback F) (representative z)) E

lemma perimeter_measurable (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have hle (a : LatticeIsometry) {A : Set Torus} (hA : MeasurableSet A) :
      perimeter (a.torus ⁻¹' A)≤perimeter A := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    rw [a.flux hF hA]
    exact le_iSup₂_of_le (a.symm.pullback F) (a.symm.pullback_admissible hF) le_rfl
  apply le_antisymm (hle e hE)
  have hh := hle e.symm (hE.preimage e.torus.continuous.measurable)
  have hset : e.symm.torus ⁻¹' (e.torus ⁻¹' E)=E := by
    ext x
    change e.torus (e.torus.symm x)∈E ↔ x∈E
    rw [e.torus.apply_symm_apply]
  rwa [hset] at hh

theorem perimeter_eq (e : LatticeIsometry) {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [←perimeter_congr_ae hp,←perimeter_congr_ae he]
  exact e.perimeter_measurable (measurableSet_toMeasurable _ _)

lemma finitePerimeter (e : LatticeIsometry) {E : Set Torus} (hE : FinitePerimeter E) :
    FinitePerimeter (e.torus ⁻¹' E) :=
  ⟨hE.1.preimage e.measurePreserving.quasiMeasurePreserving,by rw [e.perimeter_eq hE.1]; exact hE.2⟩

theorem isMinimizerAt (e : LatticeIsometry) {V : ℝ} {E : Set Torus} (hE : IsMinimizerAt V E) :
    IsMinimizerAt V (e.torus ⁻¹' E) := by
  refine ⟨e.finitePerimeter hE.1,?_,?_⟩
  · rw [e.measurePreserving.measure_preimage hE.1.1,hE.2.1]
  · intro F hF hv
    rw [e.perimeter_eq hE.1.1]
    exact hE.2.2 F hF hv

end LatticeIsometry

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarWeakGradient
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
namespace CenteredJacobiChart
variable {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}

lemma weight_smooth (c : CenteredJacobiChart E μ N) : ContDiff ℝ (⊤ : ℕ∞) c.weight :=
  cmcWeight_contDiff.comp (plane_gradient_contDiff c.smooth)

end CenteredJacobiChart
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NodalTorusScalar
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

lemma localMin_second_derivative_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0≤deriv (deriv f) x := by
  by_contra hn
  have hh : deriv (deriv f) x<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hh hmin.deriv_eq_zero hc
  have he : f=ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hmin,hmax] with y h₁ h₂
    exact le_antisymm h₂ h₁
  have hde : deriv f=ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [he.deriv] with y hy
    simpa only [deriv_const] using hy
  have hz : deriv (deriv f) x=0 := by rw [hde.deriv_eq,deriv_const]
  linarith

lemma plane_localMin_hessian_nonneg {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane} (hm : IsLocalMin f x) (v : Plane) :
    0≤⟪fderiv ℝ (gradient f) x v,v⟫ := by
  let γ : ℝ → Plane := fun t ↦ x+t•v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, id_eq, one_smul] using (hasDerivAt_id t).smul_const v |>.const_add x
  have hγc : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hm' : IsLocalMin (f ∘ γ) (0 : ℝ) :=
    (show IsLocalMin f (γ 0) by simpa only [γ,zero_smul,add_zero] using hm).comp_continuous
      hγc.continuous.continuousAt
  have hd (t : ℝ) : deriv (f ∘ γ) t=fderiv ℝ f (γ t) v :=
    ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdall : deriv (f ∘ γ)=fun t ↦ fderiv ℝ f (γ t) v := funext hd
  have hcf : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ f y v) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd : deriv (deriv (f ∘ γ)) 0=
      fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v := by
    rw [hdall]
    have he := ((hcf.differentiable (by simp) (γ 0)).hasFDerivAt.comp_hasDerivAt 0 (hγ 0)).deriv
    simpa only [γ,zero_smul,add_zero,Function.comp_def] using he
  have hn := localMin_second_derivative_nonneg hm' (hf.continuous.comp hγc.continuous).continuousAt
  rw [hdd] at hn
  rwa [plane_hessian_direction hf,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTrace_smul (a : ℝ) (L : Plane →L[ℝ] Plane) :
    planeTrace (a • L)=a*planeTrace L := by
  simp only [planeTrace,smul_apply,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum]

lemma planeTrace_cmc_nonneg (p : Plane) (L : Plane →L[ℝ] Plane)
    (hL : ∀ v : Plane,0≤⟪L v,v⟫) : 0≤planeTrace ((cmcJacobian p).comp L) := by
  let C := cmcCompress p
  have he : (cmcJacobian p).comp L=(cmcWeight p)⁻¹ • (C.comp (C.comp L)) := by
    ext v i
    simp only [ContinuousLinearMap.comp_apply,smul_apply,cmcJacobian_compress,C]
  have ht : planeTrace (C.comp (C.comp L))=planeTrace (C.comp (L.comp C)) := by
    rw [planeTrace_comp_comm C (C.comp L)]
    congr 1
  rw [he,planeTrace_smul,ht]
  apply mul_nonneg (inv_nonneg.mpr (cmcWeight_pos p).le)
  unfold planeTrace
  simp only [ContinuousLinearMap.comp_apply]
  apply Finset.sum_nonneg
  intro i _
  have hh := hL (C (EuclideanSpace.single i 1))
  have hi := cmcCompress_symm p (L (C (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1)
  have hi' : (C (L (C (EuclideanSpace.single i 1)))) i=
      ⟪L (C (EuclideanSpace.single i 1)),C (EuclideanSpace.single i 1)⟫ := by
    simpa only [C,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using hi
  rw [hi']
  exact hh

lemma plane_gradient_eq_zero_of_localMin {f : Plane → ℝ} {x : Plane}
    (hm : IsLocalMin f x) : gradient f x=0 := by
  simp only [gradient,hm.fderiv_eq_zero,map_zero]

lemma cmc_divergence_nonneg_at_localMin {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} (hm : IsLocalMin f x) :
    0≤planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x := by
  rw [planeDivergence_eq_trace,
    fderiv_clm_apply (show DifferentiableAt ℝ (fun y ↦ cmcJacobian (p y)) x from
      (cmcJacobian_contDiff.comp hp).differentiable (by simp) x)
      ((plane_gradient_contDiff hf).differentiable (by simp) x),
    plane_gradient_eq_zero_of_localMin hm,map_zero,add_zero]
  exact planeTrace_cmc_nonneg _ _ (plane_localMin_hessian_nonneg hf hm)

lemma cmc_strict_minimum_principle {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K U : Set Plane} (hK : IsCompact K) (hU : IsOpen U) (hUK : U⊆K)
    (hb : ∀ x∈K,x∉U → 0≤f x)
    (hL : ∀ x∈U,planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x<0) :
    ∀ x∈K,0≤f x := by
  intro x hx
  by_contra hn
  have hn' : f x<0 := lt_of_not_ge hn
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn ⟨x,hx⟩ hf.continuous.continuousOn
  have hneg : f z<0 := lt_of_le_of_lt (hmin hx) hn'
  have hzu : z∈U := by
    by_contra hzout
    exact (not_le.mpr hneg) (hb z hz hzout)
  have hm : IsLocalMin f z := hmin.isLocalMin (mem_of_superset (hU.mem_nhds hzu) hUK)
  exact (not_lt_of_ge (cmc_divergence_nonneg_at_localMin hp hf hm)) (hL z hzu)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeRadialExp_contDiff (a : Plane) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeRadialExp a k) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ y-a) := contDiff_id.sub contDiff_const
  exact (contDiff_const.mul (hh.norm_sq ℝ)).exp

lemma planeRadialExp_pos (a : Plane) (k : ℝ) (y : Plane) : 0<planeRadialExp a k y :=
  Real.exp_pos _

lemma planeRadialExp_gradient (a : Plane) (k : ℝ) (y : Plane) :
    gradient (planeRadialExp a k) y=(-2*k*planeRadialExp a k y) • (y-a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hh := ((((hasFDerivAt_id y).sub_const a).norm_sq).const_mul (-k)).exp.fderiv
  change fderiv ℝ (planeRadialExp a k) y=_ at hh
  rw [hh]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    innerSL_apply_apply,smul_eq_mul,real_inner_smul_left,planeRadialExp,id_eq]
  ring

lemma planeDivergence_const_smul {F : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (c : ℝ) :
    planeDivergence (fun z ↦ c • F z) y=c*planeDivergence F y := by
  rw [planeDivergence_smul (differentiableAt_const c) hF,gradient_fun_const,inner_zero_left,add_zero]

lemma sibling_planeDivergence_contDiff {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (planeDivergence F) := by
  unfold planeDivergence
  exact (((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.comp
      ((hF.fderiv_right (by simp)).clm_apply contDiff_const)))

lemma planeRadialExp_cmc_divergence {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (a : Plane) (k : ℝ) (y : Plane) :
    planeDivergence (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z)) y=
      planeRadialExp a k y*(4*k^2*⟪y-a,cmcJacobian (p y) (y-a)⟫-
        2*k*planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y) := by
  let F : Plane → Plane := fun z ↦ cmcJacobian (p z) (z-a)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (cmcJacobian_contDiff.comp hp).clm_apply (contDiff_id.sub contDiff_const)
  have he : (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z))=
      (fun z ↦ (-2*k) • (planeRadialExp a k z • F z)) := by
    funext z
    rw [planeRadialExp_gradient,map_smul,smul_smul]
  rw [he,planeDivergence_const_smul
    (show DifferentiableAt ℝ (fun z ↦ planeRadialExp a k z • F z) y from
      ((planeRadialExp_contDiff a k).smul hF).differentiable (by simp) y),
    planeDivergence_smul ((planeRadialExp_contDiff a k).differentiable (by simp) y)
      (hF.differentiable (by simp) y),planeRadialExp_gradient,real_inner_smul_left]
  change (-2*k)*(planeRadialExp a k y*planeDivergence F y+
    (-2*k*planeRadialExp a k y)*⟪y-a,F y⟫)=_
  dsimp only [F]
  ring

lemma planeRadialExp_cmc_positive {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) {a y : Plane} {R k M : ℝ}
    (hR : 0<R) (hk : 0<k) (hkM : 16*M<k*R^2)
    (hy : R/2≤‖y-a‖) (hpy : ‖p y‖≤1)
    (hD : planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y≤M) :
    0<planeDivergence (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z)) y := by
  rw [planeRadialExp_cmc_divergence hp]
  apply mul_pos (planeRadialExp_pos _ _ _)
  have hA := cmcJacobian_coercive hpy (y-a)
  have hn : R^2≤4*‖y-a‖^2 := by nlinarith [norm_nonneg (y-a)]
  have hmul := mul_le_mul_of_nonneg_left (show R^2≤32*⟪y-a,cmcJacobian (p y) (y-a)⟫ by linarith) hk.le
  have hi : 0<2*k*⟪y-a,cmcJacobian (p y) (y-a)⟫-
      planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y := by nlinarith
  convert mul_pos (by positivity : 0<2*k) hi using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_linear {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (c d : ℝ) :
    gradient (fun y ↦ f y+c*g y+d) x=gradient f x+c • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,real_inner_smul_left]
  simp only [inner_gradient_left,fderiv_add_const,
    fderiv_fun_add hf (hg.const_mul c),fderiv_const_mul hg c,add_apply,smul_apply,smul_eq_mul]

lemma cmc_divergence_linear {p : Plane → Plane} {f g : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c d : ℝ) (x : Plane) :
    planeDivergence (fun y ↦ cmcJacobian (p y) (gradient (fun z ↦ f z+c*g z+d) y)) x=
      planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x+
        c*planeDivergence (fun y ↦ cmcJacobian (p y) (gradient g y)) x := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (p y) (gradient f y)) :=
    (cmcJacobian_contDiff.comp hp).clm_apply (plane_gradient_contDiff hf)
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (p y) (gradient g y)) :=
    (cmcJacobian_contDiff.comp hp).clm_apply (plane_gradient_contDiff hg)
  have he : (fun y ↦ cmcJacobian (p y) (gradient (fun z ↦ f z+c*g z+d) y))=
      (fun y ↦ cmcJacobian (p y) (gradient f y)+c • cmcJacobian (p y) (gradient g y)) := by
    funext y
    rw [plane_gradient_linear (hf.differentiable (by simp) y)
      (hg.differentiable (by simp) y),map_add,map_smul]
  rw [he,planeDivergence_add (hF.differentiable (by simp) x)
    (show DifferentiableAt ℝ (fun y ↦ c • cmcJacobian (p y) (gradient g y)) x from
      (hG.differentiable (by simp) x).const_smul c),
    planeDivergence_const_smul (hG.differentiable (by simp) x)]

theorem cmc_annulus_barrier {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a : Plane} {R : ℝ} (hR : 0<R)
    (hpb : ∀ y∈Metric.closedBall a R,‖p y‖≤1)
    (hpos : ∀ y∈Metric.ball a R,0<f y)
    (hL : ∀ y∈Metric.ball a R,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0) :
    ∃ k c : ℝ,0<k ∧ 0 < c ∧ ∀ y∈Metric.closedBall a R,
      R/2≤‖y-a‖ → c*(planeRadialExp a k y-Real.exp (-k*R^2))≤f y := by
  have hnonneg : ∀ y∈Metric.closedBall a R,0≤f y := by
    have hs : closure (Metric.ball a R)⊆{y | 0≤f y} :=
      (isClosed_le continuous_const hf.continuous).closure_subset_iff.mpr
        (fun y hy ↦ (hpos y hy).le)
    rwa [closure_ball a hR.ne'] at hs
  obtain ⟨c,hc,hcf⟩ := (isCompact_closedBall a (R/2)).exists_forall_le'
    hf.continuous.continuousOn (fun y hy ↦ hpos y (show dist y a<R from
      lt_of_le_of_lt (show dist y a≤R/2 from hy) (by linarith)))
  let F : Plane → Plane := fun z ↦ cmcJacobian (p z) (z-a)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (cmcJacobian_contDiff.comp hp).clm_apply (contDiff_id.sub contDiff_const)
  obtain ⟨M,hM⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (sibling_planeDivergence_contDiff hF).continuous.continuousOn
  let k : ℝ := 16*(|M|+1)/R^2
  have hk : 0<k := div_pos (by positivity) (sq_pos_of_pos hR)
  have hkM : 16*M<k*R^2 := by
    have he : k*R^2=16*(|M|+1) := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hR))
    rw [he]
    linarith [le_abs_self M]
  let q := planeRadialExp a k
  let d := c*Real.exp (-k*R^2)
  let h : Plane → ℝ := fun y ↦ f y+(-c)*q y+d
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := planeRadialExp_contDiff a k
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (hf.add (contDiff_const.mul hq)).add contDiff_const
  let K := Metric.closedBall a R \ Metric.ball a (R/2)
  let U := Metric.ball a R \ Metric.closedBall a (R/2)
  have hK : IsCompact K := (isCompact_closedBall a R).diff Metric.isOpen_ball
  have hU : IsOpen U := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hUK : U⊆K := by
    intro y hy
    exact ⟨Metric.ball_subset_closedBall hy.1,fun hh ↦ hy.2 (Metric.ball_subset_closedBall hh)⟩
  have hb : ∀ y∈K,y∉U → 0≤h y := by
    intro y hy hyout
    have hyo : ‖y-a‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy.1
    have hyi : R/2≤‖y-a‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hy.2
    have hcase : ‖y-a‖=R ∨ ‖y-a‖=R/2 := by
      by_contra hn
      push Not at hn
      exact hyout ⟨by simpa only [Metric.mem_ball,dist_eq_norm] using lt_of_le_of_ne hyo hn.1,
        by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using lt_of_le_of_ne hyi (Ne.symm hn.2)⟩
    rcases hcase with ho|hi
    · have hqe : q y=Real.exp (-k*R^2) := by simp only [q,planeRadialExp,ho]
      have hfy := hnonneg y hy.1
      dsimp only [h,d]
      rw [hqe]
      linarith
    · have hfy := hcf y (by simpa only [Metric.mem_closedBall,dist_eq_norm,hi] using (le_refl (R/2)))
      have hqb : q y≤1 := by
        change Real.exp (-k*‖y-a‖^2)≤1
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sq_nonneg _))
      have hd : 0≤d := mul_nonneg hc.le (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_left hqb hc.le
      dsimp only [h]
      nlinarith
  have hstrict : ∀ y∈U,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient h z)) y<0 := by
    intro y hy
    have hD : planeDivergence F y≤M := (le_abs_self _).trans (hM y (Metric.ball_subset_closedBall hy.1))
    have hrad := planeRadialExp_cmc_positive hp hR hk hkM
      (show R/2≤‖y-a‖ from le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hy.2))
      (hpb y (Metric.ball_subset_closedBall hy.1)) hD
    dsimp only [h]
    rw [cmc_divergence_linear hp hf hq,hL y hy.1,zero_add]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hrad
  have hbound := cmc_strict_minimum_principle hp hh hK hU hUK hb hstrict
  refine ⟨k,c,hk,hc,?_⟩
  intro y hy hyi
  have hh := hbound y ⟨hy,by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hyi⟩
  dsimp only [h,d,q] at hh
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_annulus_radial_tangent {a x : Plane} {R : ℝ}
    (hR : 0<R) (hx : ‖x-a‖=R) :
    segment ℝ x (x+(1/2 : ℝ) • (a-x))⊆
      Metric.closedBall a R \ Metric.ball a (R/2) := by
  rw [segment_eq_image']
  rintro y ⟨t,ht,rfl⟩
  have he : x+t • (x+(1/2 : ℝ) • (a-x)-x)-a=(1-t/2) • (x-a) := by module
  have hn : ‖x+t • (x+(1/2 : ℝ) • (a-x)-x)-a‖=(1-t/2)*R := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2]),hx]
  constructor
  · simp only [Metric.mem_closedBall,dist_eq_norm,hn]
    nlinarith [ht.1]
  · simp only [Metric.mem_ball,dist_eq_norm,hn,not_lt]
    nlinarith [ht.2]

lemma radial_barrier_inward_derivative {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {a x : Plane} {R k c : ℝ}
    (hR : 0<R) (hk : 0<k) (hc : 0 < c) (hx : ‖x-a‖=R) (hfx : f x=0)
    (hb : ∀ y∈Metric.closedBall a R,R/2≤‖y-a‖ →
      c*(planeRadialExp a k y-Real.exp (-k*R^2))≤f y) :
    0<fderiv ℝ f x (a-x) := by
  let q := planeRadialExp a k
  let d := c*Real.exp (-k*R^2)
  let h : Plane → ℝ := fun y ↦ f y+(-c)*q y+d
  let K := Metric.closedBall a R \ Metric.ball a (R/2)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := planeRadialExp_contDiff a k
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (hf.add (contDiff_const.mul hq)).add contDiff_const
  have hqx : q x=Real.exp (-k*R^2) := by simp only [q,planeRadialExp,hx]
  have hxzero : h x=0 := by dsimp only [h,d]; rw [hfx,hqx]; ring
  have hm : IsMinOn h K x := by
    intro y hy
    rw [hxzero]
    have hby := hb y hy.1 (by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hy.2)
    change 0 ≤ f y+(-c)*planeRadialExp a k y+c*Real.exp (-k*R^2)
    linarith only [hby]
  have htan := sub_mem_posTangentConeAt_of_segment_subset (plane_annulus_radial_tangent hR hx)
  have hder := hm.localize.hasFDerivWithinAt_nonneg
    ((hh.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) htan
  have hgrad : gradient h x=gradient f x+(-c) • ((-2*k*q x) • (x-a)) := by
    dsimp only [h]
    rw [plane_gradient_linear (hf.differentiable (by simp) x) (hq.differentiable (by simp) x)]
    rw [show gradient q x=(-2*k*q x) • (x-a) from planeRadialExp_gradient a k x]
  have hi : ⟪x-a,a-x⟫= -R^2 := by
    rw [show a-x= -(x-a) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hx]
  rw [← inner_gradient_left,hgrad] at hder
  simp only [add_sub_cancel_left,inner_add_left,real_inner_smul_left,real_inner_smul_right,
    inner_gradient_left,hi,map_smul,smul_eq_mul] at hder
  have hp := mul_pos (mul_pos (mul_pos hc hk) (planeRadialExp_pos a k x)) (sq_pos_of_pos hR)
  change 0 < c*k*q x*R^2 at hp
  nlinarith

theorem cmc_hopf_inward_derivative {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a x : Plane} {R : ℝ} (hR : 0<R) (hx : ‖x-a‖=R) (hfx : f x=0)
    (hpb : ∀ y∈Metric.closedBall a R,‖p y‖≤1)
    (hpos : ∀ y∈Metric.ball a R,0<f y)
    (hL : ∀ y∈Metric.ball a R,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0) :
    0<fderiv ℝ f x (a-x) := by
  obtain ⟨k,c,hk,hc,hb⟩ := cmc_annulus_barrier hp hf hR hpb hpos hL
  exact radial_barrier_inward_derivative hf hR hk hc hx hfx hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma CenteredJacobiChart.parameter_zero
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) : c.parameter 0=cubeCenter := by
  simp only [CenteredJacobiChart.parameter,normalGraph,c.zero,zero_smul,add_zero]
  change cubeCenter+(normalPlaneLinearIsometry c.n) 0=cubeCenter
  rw [map_zero,add_zero]

lemma CenteredJacobiChart.closure_pullback
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) {D : Set Torus}
    (hD : D⊆frontier (openRepresentative E))
    (hcl : quotientMap cubeCenter∈closure D) {r : ℝ} (hr : 0 < r) :
    (0 : Plane)∈closure (Metric.ball (0 : Plane) r∩
      (fun y ↦ quotientMap (c.parameter y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp c.cover_germ
  let t := min δ (min r ε)
  have ht : 0<t := lt_min hδ (lt_min hr hε)
  obtain ⟨b,hbD,hb⟩ := Metric.mem_closure_iff.mp hcl t ht
  have hbball : b∈Metric.ball (quotientMap cubeCenter) t := by
    simpa only [Metric.mem_ball,dist_comm] using hb
  rw [← quotientMap_image_ball cubeCenter t] at hbball
  obtain ⟨z,hz,hzb⟩ := hbball
  let v := z-cubeCenter
  have hv : ‖v‖<t := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hvδ : v∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_le (min_le_left _ _)
  have hsurf : quotientMap (cubeCenter+v)∈frontier (openRepresentative E) := by
    simpa only [v,add_sub_cancel,hzb] using hD hbD
  have he := (hδsub hvδ).mp hsurf
  let y := normalPlaneCoordinates c.n v
  have hy : ‖y‖<t := (normalPlaneCoordinates_norm_le _ _).trans_lt hv
  refine ⟨y,⟨?_,?_⟩,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using
      hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · change quotientMap (cubeCenter+normalGraph c.n c.g y)∈D
    rw [he]
    simpa only [v,add_sub_cancel,hzb] using hbD
  · simpa only [dist_zero_left] using hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_planeElliptic_contDiff {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (sibling_planeElliptic A f) :=
  sibling_planeDivergence_contDiff (hA.clm_apply (plane_gradient_contDiff hf))

lemma compact_inner_left {b p : Plane → Plane} (hc : HasCompactSupport p) :
    HasCompactSupport (fun y ↦ ⟪p y,b y⟫) := by
  apply hc.mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  rw [hy,inner_zero_left]

lemma compact_inner_right {b p : Plane → Plane} (hc : HasCompactSupport p) :
    HasCompactSupport (fun y ↦ ⟪b y,p y⟫) := by
  simpa only [real_inner_comm] using compact_inner_left (b := b) hc

lemma compact_clm_apply {A : Plane → Plane →L[ℝ] Plane} {p : Plane → Plane}
    (hc : HasCompactSupport p) : HasCompactSupport (fun y ↦ A y (p y)) := by
  apply hc.mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  rw [hy,map_zero]

lemma sibling_planeDivergence_compact {F : Plane → Plane} (hc : HasCompactSupport F) :
    HasCompactSupport (planeDivergence F) := by
  have h0 : HasCompactSupport (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single 0 1)) 0) :=
    (hc.fderiv_apply ℝ _).comp_left (g := fun v : Plane ↦ v 0) (by simp)
  have h1 : HasCompactSupport (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single 1 1)) 1) :=
    (hc.fderiv_apply ℝ _).comp_left (g := fun v : Plane ↦ v 1) (by simp)
  exact h0.add h1

lemma sibling_planeElliptic_compact {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (sibling_planeElliptic A f) :=
  sibling_planeDivergence_compact (compact_clm_apply (plane_gradient_compact hc))

lemma planeElliptic_ibp {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    (∫ y,sibling_planeElliptic A f y*g y)= -(∫ y,⟪gradient g y,A y (gradient f y)⟫) := by
  simpa only [sibling_planeElliptic,inner_gradient_left] using
    plane_divergence_integration_by_parts
      ((hA.clm_apply (plane_gradient_contDiff hf)).of_le (by simp))
      (hg.of_le (by simp)) hc

lemma plane_inner_fderiv {p q : Plane → Plane} {y v : Plane}
    (hp : DifferentiableAt ℝ p y) (hq : DifferentiableAt ℝ q y) :
    fderiv ℝ (fun z ↦ ⟪p z,q z⟫) y v=
      ⟪fderiv ℝ p y v,q y⟫+⟪p y,fderiv ℝ q y v⟫ := by
  rw [(hp.hasFDerivAt.inner ℝ hq.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply]
  exact add_comm _ _

lemma plane_clm_fderiv {A : Plane → Plane →L[ℝ] Plane} {p : Plane → Plane}
    {y v : Plane} (hA : DifferentiableAt ℝ A y) (hp : DifferentiableAt ℝ p y) :
    fderiv ℝ (fun z ↦ A z (p z)) y v=(fderiv ℝ A y v) (p y)+A y (fderiv ℝ p y v) := by
  rw [(hA.hasFDerivAt.clm_apply hp.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma plane_energy_fderiv {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (y v : Plane) :
    fderiv ℝ (fun z ↦ ⟪gradient f z,A z (gradient f z)⟫) y v=
      2*⟪A y (gradient f y),fderiv ℝ (gradient f) y v⟫+
        ⟪gradient f y,(fderiv ℝ A y v) (gradient f y)⟫ := by
  have hp := (plane_gradient_contDiff hf).differentiable (by simp) y
  rw [plane_inner_fderiv hp ((hA.differentiable (by simp) y).clm_apply hp),
    plane_clm_fderiv (hA.differentiable (by simp) y) hp,inner_add_right,
    hAs y (gradient f y) (fderiv ℝ (gradient f) y v)]
  rw [real_inner_comm (A y (gradient f y))]
  ring

lemma plane_transport_gradient {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y q : Plane) :
    ⟪gradient (fun z ↦ ⟪b z,gradient f z⟫) y,q⟫=
      ⟪gradient f y,fderiv ℝ b y q⟫+
        ⟪q,fderiv ℝ (gradient f) y (b y)⟫ := by
  rw [inner_gradient_left,plane_inner_fderiv (hb.differentiable (by simp) y)
    ((plane_gradient_contDiff hf).differentiable (by simp) y),
    real_inner_comm (fderiv ℝ b y q),← plane_hessian_symmetric hf,
    real_inner_comm (fderiv ℝ (gradient f) y (b y))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTransport_contDiff {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (planeTransport b f) :=
  (contDiff_const.mul (hb.inner ℝ (plane_gradient_contDiff hf))).add
    ((sibling_planeDivergence_contDiff hb).mul hf)

lemma planeTransport_compact {b : Plane → Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeTransport b f) :=
  (compact_inner_right (plane_gradient_compact hc)).mul_left.add hc.mul_left

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SiblingPlaneCarlemanS
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

lemma plane_elliptic_weight_identity {A : Plane → Plane →L[ℝ] Plane}
    {f c : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*(c y*f y))=
      -(∫ y,c y*⟪gradient f y,A y (gradient f y)⟫)+
        (1/2)*(∫ y,sibling_planeElliptic A c y*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hq := hA.clm_apply hp
  have hr := plane_gradient_contDiff hc
  have hpc := plane_gradient_compact hfc
  have hi : Integrable (fun y ↦ c y*⟪gradient f y,A y (gradient f y)⟫) :=
    (hc.continuous.mul (hp.continuous.inner hq.continuous)).integrable_of_hasCompactSupport
      (compact_inner_left hpc).mul_left
  have hj : Integrable (fun y ↦ f y*⟪gradient c y,A y (gradient f y)⟫) :=
    (hf.continuous.mul (hr.continuous.inner hq.continuous)).integrable_of_hasCompactSupport
      hfc.mul_right
  have he (y : Plane) : ⟪gradient (fun z ↦ c z*f z) y,A y (gradient f y)⟫=
      c y*⟪gradient f y,A y (gradient f y)⟫+
        f y*⟪gradient c y,A y (gradient f y)⟫ := by
    rw [plane_gradient_mul (hc.differentiable (by simp) y)
      (hf.differentiable (by simp) y),inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have h1 := planeElliptic_ibp hA hf (hc.mul hf) hfc.mul_left
  simp_rw [he] at h1
  rw [integral_add hi hj] at h1
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ (f y)^2) := hf.pow 2
  have he2 (y : Plane) : ⟪gradient (fun z ↦ (f z)^2) y,A y (gradient c y)⟫=
      2*(f y*⟪gradient c y,A y (gradient f y)⟫) := by
    simp only [pow_two]
    rw [plane_gradient_mul (hf.differentiable (by simp) y)
      (hf.differentiable (by simp) y),inner_add_left,real_inner_smul_left,
      hAs y (gradient f y) (gradient c y)]
    ring
  have h2 := planeElliptic_ibp hA hc hf2 (hfc.comp_left (g := fun r : ℝ ↦ r^2) (by simp))
  simp_rw [he2] at h2
  rw [integral_const_mul] at h2
  linarith

lemma plane_elliptic_transport_identity {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} {b : Plane → Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*⟪b y,gradient f y⟫)=
      -(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)+
      (1/2)*(∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)+
      (1/2)*(∫ y,planeDivergence b y*⟪gradient f y,A y (gradient f y)⟫) := by
  have hp := plane_gradient_contDiff hf
  have hq := hA.clm_apply hp
  have hpc := plane_gradient_compact hfc
  have hqc := compact_clm_apply hpc (A := A)
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdp : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (gradient f)) := hp.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  have hi : Integrable (fun y ↦ ⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫) :=
    (hp.continuous.inner (hdb.clm_apply hq).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hpc)
  have hj : Integrable (fun y ↦ ⟪A y (gradient f y),fderiv ℝ (gradient f) y (b y)⟫) :=
    (hq.continuous.inner (hdp.clm_apply hb).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hqc)
  have hk : Integrable (fun y ↦ ⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫) :=
    (hp.continuous.inner ((hdA.clm_apply hb).clm_apply hp).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hpc)
  have h1 := planeElliptic_ibp hA hf (hb.inner ℝ hp) (compact_inner_right hpc)
  simp_rw [plane_transport_gradient hb hf] at h1
  rw [integral_add hi hj] at h1
  have he := plane_divergence_integration_by_parts (hb.of_le (by simp))
    ((hp.inner ℝ hq).of_le (by simp)) (compact_inner_left hpc)
  simp_rw [plane_energy_fderiv hA hf hAs] at he
  rw [integral_add (hj.const_mul 2) hk,integral_const_mul] at he
  linarith

theorem plane_rellich_identity {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} {b : Plane → Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*planeTransport b f y)=
      -2*(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)+
      (∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)+
      (1/2)*(∫ y,sibling_planeElliptic A (planeDivergence b) y*(f y)^2) := by
  have hL := sibling_planeElliptic_contDiff hA hf
  have hi : Integrable (fun y ↦ sibling_planeElliptic A f y*⟪b y,gradient f y⟫) :=
    (hL.continuous.mul (hb.inner ℝ (plane_gradient_contDiff hf)).continuous).integrable_of_hasCompactSupport
      (compact_inner_right (plane_gradient_compact hfc)).mul_left
  have hj : Integrable (fun y ↦ sibling_planeElliptic A f y*(planeDivergence b y*f y)) :=
    (hL.continuous.mul ((sibling_planeDivergence_contDiff hb).mul hf).continuous).integrable_of_hasCompactSupport
      hfc.mul_left.mul_left
  have he (y : Plane) : sibling_planeElliptic A f y*planeTransport b f y=
      2*(sibling_planeElliptic A f y*⟪b y,gradient f y⟫)+
        sibling_planeElliptic A f y*(planeDivergence b y*f y) := by
    dsimp [planeTransport]; ring
  simp_rw [he]
  rw [integral_add (hi.const_mul 2) hj,integral_const_mul]
  rw [plane_elliptic_transport_identity hA hf hb hfc hAs,
    plane_elliptic_weight_identity hA hf (sibling_planeDivergence_contDiff hb) hfc hAs]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeCarlemanS_contDiff {A : Plane → Plane →L[ℝ] Plane} {a f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sibling_planeCarlemanS A a τ f) :=
  (sibling_planeElliptic_contDiff hA hf).add ((contDiff_const.mul ha).mul hf)

lemma planeCarlemanS_compact {A : Plane → Plane →L[ℝ] Plane} {a f : Plane → ℝ}
    (hc : HasCompactSupport f) (τ : ℝ) : HasCompactSupport (sibling_planeCarlemanS A a τ f) :=
  (sibling_planeElliptic_compact hc).add hc.mul_left

lemma plane_transport_weight_identity {a f : Plane → ℝ} {b : Plane → Plane}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport f) :
    (∫ y,a y*f y*planeTransport b f y)=
      -(∫ y,⟪gradient a y,b y⟫*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hq := plane_gradient_contDiff ha
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hi : Integrable (fun y ↦ a y*f y*⟪b y,gradient f y⟫) :=
    ((ha.mul hf).continuous.mul (hb.inner ℝ hp).continuous).integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  have hj : Integrable (fun y ↦ planeDivergence b y*(a y*(f y)^2)) :=
    ((sibling_planeDivergence_contDiff hb).continuous.mul (ha.mul (hf.pow 2)).continuous).integrable_of_hasCompactSupport
      hc2.mul_left.mul_left
  have hk : Integrable (fun y ↦ ⟪gradient a y,b y⟫*(f y)^2) :=
    ((hq.inner ℝ hb).continuous.mul (hf.pow 2).continuous).integrable_of_hasCompactSupport
      hc2.mul_left
  have htest := ha.mul (hf.pow 2)
  have heb (y : Plane) : fderiv ℝ (fun z ↦ a z*(f z)^2) y (b y)=
      2*(a y*f y*⟪b y,gradient f y⟫)+⟪gradient a y,b y⟫*(f y)^2 := by
    rw [← inner_gradient_left,plane_gradient_mul (ha.differentiable (by simp) y)
      ((hf.pow 2).differentiable (by simp) y)]
    simp only [pow_two]
    rw [plane_gradient_mul (hf.differentiable (by simp) y)
      (hf.differentiable (by simp) y)]
    simp only [inner_add_left,real_inner_smul_left]
    rw [real_inner_comm (gradient f y)]
    ring
  have he := plane_divergence_integration_by_parts (hb.of_le (by simp))
    (htest.of_le (by simp)) hc2.mul_left
  simp_rw [heb] at he
  rw [integral_add (hi.const_mul 2) hk, integral_const_mul] at he
  have he' (y : Plane) : a y*f y*planeTransport b f y=
      2*(a y*f y*⟪b y,gradient f y⟫)+planeDivergence b y*(a y*(f y)^2) := by
    dsimp [planeTransport]; ring
  simp_rw [he']
  rw [integral_add (hi.const_mul 2) hj,integral_const_mul]
  linarith

theorem plane_carleman_identity {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) :
    (∫ y,(sibling_planeCarlemanP A b a τ f y)^2)=
      (∫ y,(sibling_planeCarlemanS A a τ f y)^2)+τ^2*(∫ y,(planeTransport b f y)^2)+
      4*τ*(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)-
      2*τ*(∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)-
      τ*(∫ y,sibling_planeElliptic A (planeDivergence b) y*(f y)^2)+
      2*τ^3*(∫ y,⟪gradient a y,b y⟫*(f y)^2) := by
  have hS := planeCarlemanS_contDiff hA ha hf τ
  have hT := planeTransport_contDiff hb hf
  have hL := sibling_planeElliptic_contDiff hA hf
  have hcS := planeCarlemanS_compact (A := A) (a := a) hc τ
  have hcT := planeTransport_compact (b := b) hc
  have hSS : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2) :=
    (hS.pow 2).continuous.integrable_of_hasCompactSupport
      (hcS.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have hTT : Integrable (fun y ↦ (planeTransport b f y)^2) :=
    (hT.pow 2).continuous.integrable_of_hasCompactSupport
      (hcT.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have hLT : Integrable (fun y ↦ sibling_planeElliptic A f y*planeTransport b f y) :=
    (hL.mul hT).continuous.integrable_of_hasCompactSupport hcT.mul_left
  have haT : Integrable (fun y ↦ a y*f y*planeTransport b f y) :=
    ((ha.mul hf).mul hT).continuous.integrable_of_hasCompactSupport hcT.mul_left
  have he (y : Plane) : (sibling_planeCarlemanP A b a τ f y)^2=
      (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2-
      2*τ*(sibling_planeElliptic A f y*planeTransport b f y)-
      2*τ^3*(a y*f y*planeTransport b f y) := by
    dsimp [sibling_planeCarlemanP,sibling_planeCarlemanS]; ring
  simp_rw [he]
  have hi1 : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2) :=
    hSS.add (hTT.const_mul (τ^2))
  have hi2 : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2-
      2*τ*(sibling_planeElliptic A f y*planeTransport b f y)) := hi1.sub (hLT.const_mul (2*τ))
  rw [integral_sub hi2 (haT.const_mul (2*τ^3)),
    integral_sub hi1 (hLT.const_mul (2*τ)),
    integral_add hSS (hTT.const_mul (τ^2))]
  simp only [integral_const_mul]
  rw [plane_rellich_identity hA hf hb hc hAs,plane_transport_weight_identity ha hf hb hc]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_scaled_exp {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (t : ℝ) (y : Plane) :
    gradient (fun z ↦ Real.exp (t*φ z)) y=(t*Real.exp (t*φ y)) • gradient φ y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [(((hφ.differentiable (by simp) y).hasFDerivAt.const_mul t).exp).fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma planeElliptic_product {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (y : Plane) : sibling_planeElliptic A (fun z ↦ f z*g z) y=
      f y*sibling_planeElliptic A g y+g y*sibling_planeElliptic A f y+
        2*⟪gradient f y,A y (gradient g y)⟫ := by
  have hp := hA.clm_apply (plane_gradient_contDiff hf)
  have hq := hA.clm_apply (plane_gradient_contDiff hg)
  have he : (fun z ↦ A z (gradient (fun x ↦ f x*g x) z))=
      (fun z ↦ f z • A z (gradient g z)+g z • A z (gradient f z)) := by
    funext z
    rw [plane_gradient_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z),
      map_add,map_smul,map_smul]
  have hs1 : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ f z • A z (gradient g z)) := hf.smul hq
  have hs2 : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ g z • A z (gradient f z)) := hg.smul hp
  unfold sibling_planeElliptic
  rw [he,planeDivergence_add (hs1.differentiable (by simp) y)
    (hs2.differentiable (by simp) y),
    planeDivergence_smul (hf.differentiable (by simp) y) (hq.differentiable (by simp) y),
    planeDivergence_smul (hg.differentiable (by simp) y) (hp.differentiable (by simp) y),
    hAs y (gradient g y) (gradient f y)]
  ring

lemma planeElliptic_scaled_exp {A : Plane → Plane →L[ℝ] Plane} {φ : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : ℝ) (y : Plane) :
    sibling_planeElliptic A (fun z ↦ Real.exp (t*φ z)) y=
      Real.exp (t*φ y)*(t*sibling_planeElliptic A φ y+t^2*⟪gradient φ y,A y (gradient φ y)⟫) := by
  have hq := hA.clm_apply (plane_gradient_contDiff hφ)
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ t*Real.exp (t*φ z)) :=
    contDiff_const.mul (contDiff_const.mul hφ).exp
  have he : (fun z ↦ A z (gradient (fun x ↦ Real.exp (t*φ x)) z))=
      (fun z ↦ (t*Real.exp (t*φ z)) • A z (gradient φ z)) := by
    funext z
    rw [plane_gradient_scaled_exp hφ,map_smul]
  unfold sibling_planeElliptic
  rw [he,planeDivergence_smul (hh.differentiable (by simp) y) (hq.differentiable (by simp) y)]
  have hg : gradient (fun z ↦ t*Real.exp (t*φ z)) y=
      (t^2*Real.exp (t*φ y)) • gradient φ y := by
    rw [plane_gradient_mul (differentiableAt_const _)
      (((contDiff_const.mul hφ).exp).differentiable (by simp) y),
      gradient_fun_const,smul_zero,add_zero,plane_gradient_scaled_exp hφ,smul_smul]
    congr 1
    ring
  rw [hg,real_inner_smul_left]
  ring

theorem plane_elliptic_conjugation {A : Plane → Plane →L[ℝ] Plane} {φ f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (τ : ℝ) (y : Plane) :
    sibling_planeCarlemanP A (fun z ↦ A z (gradient φ z))
      (fun z ↦ ⟪gradient φ z,A z (gradient φ z)⟫) τ f y=
      Real.exp (τ*φ y)*sibling_planeElliptic A (fun z ↦ Real.exp (-τ*φ z)*f z) y := by
  rw [planeElliptic_product hA ((contDiff_const.mul hφ).exp) hf hAs,
    planeElliptic_scaled_exp hA hφ,plane_gradient_scaled_exp hφ,real_inner_smul_left]
  have hcomm : ⟪gradient φ y,A y (gradient f y)⟫=⟪A y (gradient φ y),gradient f y⟫ := by
    rw [hAs,real_inner_comm]
  have he : Real.exp (τ*φ y)*Real.exp (-τ*φ y)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  rw [hcomm]
  dsimp [sibling_planeCarlemanP,sibling_planeCarlemanS,planeTransport,sibling_planeElliptic]
  linear_combination -(planeDivergence (fun z ↦ A z (gradient f z)) y+
    τ^2*⟪gradient φ y,A y (gradient φ y)⟫*f y-
    τ*(2*⟪A y (gradient φ y),gradient f y⟫+
      planeDivergence (fun z ↦ A z (gradient φ z)) y*f y))*he

theorem plane_elliptic_conjugation_forward {A : Plane → Plane →L[ℝ] Plane}
    {φ u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) (y : Plane) :
    sibling_planeCarlemanP A (fun z ↦ A z (gradient φ z))
      (fun z ↦ ⟪gradient φ z,A z (gradient φ z)⟫) τ
      (fun z ↦ Real.exp (τ*φ z)*u z) y=
      Real.exp (τ*φ y)*sibling_planeElliptic A u y := by
  rw [plane_elliptic_conjugation hA hφ ((contDiff_const.mul hφ).exp.mul hu) hAs]
  congr 2
  funext z
  rw [← mul_assoc,← Real.exp_add]
  have he : -τ*φ z+τ*φ z=0 := by ring
  rw [he,Real.exp_zero,one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeBentHessian_apply (n : Plane) (ℓ M : ℝ) (v : Plane) :
    planeBentHessian n ℓ M v=(ℓ*⟪n,v⟫) • n-M • v := by
  simp [planeBentHessian,smul_smul]

lemma planeBentHessian_symm (n : Plane) (ℓ M : ℝ) (v w : Plane) :
    ⟪v,planeBentHessian n ℓ M w⟫=⟪w,planeBentHessian n ℓ M v⟫ := by
  simp only [planeBentHessian_apply,inner_sub_right,real_inner_smul_right]
  rw [real_inner_comm v n,real_inner_comm w n,real_inner_comm v w]
  ring

lemma planeBentHessian_quadratic (n : Plane) (ℓ M : ℝ) (v : Plane) :
    ⟪v,planeBentHessian n ℓ M v⟫=ℓ*⟪n,v⟫^2-M*‖v‖^2 := by
  rw [planeBentHessian_apply,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_comm v n,real_inner_self_eq_norm_sq]
  ring

lemma planeBentWeight_formula (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    planeBentWeight x n ℓ M y= -⟪n,y-x⟫+(ℓ/2)*⟪n,y-x⟫^2-(M/2)*‖y-x‖^2 := by
  rw [planeBentWeight,planeBentHessian_quadratic]
  ring

lemma planeBentWeight_contDiff (x n : Plane) (ℓ M : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeBentWeight x n ℓ M) := by
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ y-x) := contDiff_id.sub contDiff_const
  exact (contDiff_const.inner ℝ hz).neg.add
    (contDiff_const.mul (hz.inner ℝ ((planeBentHessian n ℓ M).contDiff.comp hz)))

lemma planeBentWeight_gradient (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    gradient (planeBentWeight x n ℓ M) y= -n+planeBentHessian n ℓ M (y-x) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hz : HasFDerivAt (fun z : Plane ↦ z-x) (ContinuousLinearMap.id ℝ Plane) y :=
    (hasFDerivAt_id y).sub_const x
  have hlin := (hasFDerivAt_const n y).inner ℝ hz
  have hquad := hz.inner ℝ ((planeBentHessian n ℓ M).hasFDerivAt.comp y hz)
  have hh := (hlin.neg.add (hquad.const_mul (1/2))).fderiv
  change fderiv ℝ (planeBentWeight x n ℓ M) y=_ at hh
  rw [hh]
  simp only [add_apply,neg_apply,smul_apply,ContinuousLinearMap.comp_apply,fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply,zero_apply,ContinuousLinearMap.id_apply,
    inner_zero_left,add_zero,smul_eq_mul,inner_add_left,inner_neg_left,Function.comp_apply]
  rw [planeBentHessian_symm n ℓ M (y-x) v,
    real_inner_comm (planeBentHessian n ℓ M (y-x)) v]
  ring

lemma planeBentWeight_gradient_fderiv (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    fderiv ℝ (gradient (planeBentWeight x n ℓ M)) y=planeBentHessian n ℓ M := by
  have he : gradient (planeBentWeight x n ℓ M)=
      (fun z ↦ -n+planeBentHessian n ℓ M (z-x)) := funext (planeBentWeight_gradient x n ℓ M)
  rw [he]
  have hz : HasFDerivAt (fun z : Plane ↦ z-x) (ContinuousLinearMap.id ℝ Plane) y :=
    (hasFDerivAt_id y).sub_const x
  have hcn : HasFDerivAt (fun _ : Plane ↦ -n) (0 : Plane →L[ℝ] Plane) y :=
    hasFDerivAt_const _ _
  have hh : HasFDerivAt (fun z : Plane ↦ -n+planeBentHessian n ℓ M (z-x))
      (0+(planeBentHessian n ℓ M).comp (ContinuousLinearMap.id ℝ Plane)) y :=
    hcn.add ((planeBentHessian n ℓ M).hasFDerivAt.comp y hz)
  simpa only [zero_add,ContinuousLinearMap.comp_id] using hh.fderiv

lemma planeBentWeight_gradient_center (x n : Plane) (ℓ M : ℝ) :
    gradient (planeBentWeight x n ℓ M) x= -n := by
  simp [planeBentWeight_gradient]

lemma planeBentWeight_center (x n : Plane) (ℓ M : ℝ) : planeBentWeight x n ℓ M x=0 := by
  simp [planeBentWeight]

lemma plane_inner_clm_abs (L : Plane →L[ℝ] Plane) (p : Plane) :
    |⟪p,L p⟫|≤‖L‖*‖p‖^2 := by
  have hh := mul_le_mul_of_nonneg_left (L.le_opNorm p) (norm_nonneg p)
  have hi := abs_real_inner_le_norm p (L p)
  nlinarith

lemma plane_quadratic_coercive_near {R : Plane → Plane →L[ℝ] Plane} {x : Plane}
    (hR : ContinuousAt R x) (h0 : ∀ p : Plane,‖p‖^2≤⟪p,R x p⟫) :
    ∀ᶠ y in 𝓝 x, ∀ p : Plane,0≤⟪p,R y p⟫ := by
  have he : ∀ᶠ y in 𝓝 x,‖R y-R x‖<1 := by
    have hh : ContinuousAt (fun y ↦ R y-R x) x := hR.sub continuousAt_const
    exact (hh.norm.eventually (gt_mem_nhds (show ‖R x-R x‖<1 by simp)))
  filter_upwards [he] with y hy p
  have hdiff := neg_le_of_abs_le (plane_inner_clm_abs (R y-R x) p)
  have hb := mul_le_mul_of_nonneg_right hy.le (sq_nonneg ‖p‖)
  simp only [sub_apply,inner_sub_right] at hdiff
  nlinarith [h0 p]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_bilinear_bound (D : Plane →L[ℝ] (Plane →L[ℝ] Plane))
    (u v w : Plane) : |⟪v,(D u) w⟫|≤‖v‖*(‖D‖*‖u‖*‖w‖) := by
  calc
    _≤‖v‖*‖(D u) w‖ := abs_real_inner_le_norm _ _
    _≤‖v‖*(‖D u‖*‖w‖) := mul_le_mul_of_nonneg_left ((D u).le_opNorm w) (norm_nonneg v)
    _≤_ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg w)) (norm_nonneg v)

lemma plane_weight_center_gradient_bound {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) (ℓ M : ℝ) (hℓ : 0≤ℓ) (hM : 0≤M) (p : Plane) :
    -(6*‖fderiv ℝ A x‖*‖A x‖+4*M*‖A x‖^2)*‖p‖^2≤
      4*⟪p,fderiv ℝ (fun y ↦ A y (gradient (planeBentWeight x n ℓ M) y)) x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (A x (gradient (planeBentWeight x n ℓ M) x))) p⟫ := by
  have hφ := planeBentWeight_contDiff x n ℓ M
  rw [plane_clm_fderiv (hA.differentiable (by simp) x)
    ((plane_gradient_contDiff hφ).differentiable (by simp) x),
    planeBentWeight_gradient_center,planeBentWeight_gradient_fderiv,inner_add_right]
  have hi := plane_inner_bilinear_bound (fderiv ℝ A x) (A x p) p (-n)
  simp only [norm_neg,hn,mul_one] at hi
  have hi' : |⟪p,(fderiv ℝ A x (A x p)) (-n)⟫|≤
      ‖fderiv ℝ A x‖*‖A x‖*‖p‖^2 := by
    calc
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x p‖) := hi
      _≤‖p‖*(‖fderiv ℝ A x‖*(‖A x‖*‖p‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((A x).le_opNorm p)
          (norm_nonneg (fderiv ℝ A x))) (norm_nonneg p)
      _=_ := by ring
  have hj := plane_inner_bilinear_bound (fderiv ℝ A x) (A x (-n)) p p
  have haN : ‖A x (-n)‖≤‖A x‖ := by simpa [hn] using (A x).le_opNorm (-n)
  have hj' : |⟪p,(fderiv ℝ A x (A x (-n))) p⟫|≤
      ‖fderiv ℝ A x‖*‖A x‖*‖p‖^2 := by
    calc
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x (-n)‖*‖p‖) := hj
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x‖*‖p‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haN (norm_nonneg (fderiv ℝ A x))) (norm_nonneg p)) (norm_nonneg p)
      _=_ := by ring
  have hsym : ⟪p,A x (planeBentHessian n ℓ M (A x p))⟫=
      ℓ*⟪n,A x p⟫^2-M*‖A x p‖^2 := by
    rw [hAs,real_inner_comm,planeBentHessian_quadratic]
  have hnorm : ‖A x p‖^2≤‖A x‖^2*‖p‖^2 := by
    calc
      _≤(‖A x‖*‖p‖)^2 := by gcongr; exact (A x).le_opNorm p
      _=_ := mul_pow _ _ _
  have hMnorm := mul_le_mul_of_nonneg_left hnorm hM
  rw [hsym]
  have hpos := mul_nonneg hℓ (sq_nonneg ⟪n,A x p⟫)
  have hi0 := neg_le_of_abs_le hi'
  have hj0 := le_of_abs_le hj'
  nlinarith

lemma plane_weight_center_mass {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (ℓ M : ℝ) :
    ⟪gradient (fun y ↦ ⟪gradient (planeBentWeight x n ℓ M) y,
        A y (gradient (planeBentWeight x n ℓ M) y)⟫) x,
      A x (gradient (planeBentWeight x n ℓ M) x)⟫=
      2*ℓ*⟪n,A x n⟫^2-2*M*‖A x n‖^2+
        ⟪-n,(fderiv ℝ A x (A x (-n))) (-n)⟫ := by
  rw [inner_gradient_left,plane_energy_fderiv hA (planeBentWeight_contDiff x n ℓ M) hAs,
    planeBentWeight_gradient_center,planeBentWeight_gradient_fderiv]
  rw [planeBentHessian_quadratic]
  simp only [map_neg,inner_neg_right,norm_neg,neg_sq]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_weight_positive_center {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ k : ℝ,0 < ℓ ∧
      let φ := planeBentWeight x n ℓ M
      let b : Plane → Plane := fun y ↦ A y (gradient φ y)
      let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
      (∀ p : Plane,‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
        2*⟪p,(fderiv ℝ A x (b x)) p⟫+k*⟪p,A x p⟫) ∧
      3 < 2*⟪gradient a x,b x⟫-k*a x := by
  let K : ℝ := 6*‖fderiv ℝ A x‖*‖A x‖+4*M*‖A x‖^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let k : ℝ := (K+1)/m
  have hk : 0 < k := div_pos (by linarith) hm
  have hkm : k*m=K+1 := by dsimp [k]; field_simp
  let a0 : ℝ := ⟪n,A x n⟫
  have ha0 : 0 < a0 := by
    have hh := hco n
    rw [hn,one_pow,mul_one] at hh
    exact lt_of_lt_of_le hm hh
  let D : ℝ := ⟪-n,(fderiv ℝ A x (A x (-n))) (-n)⟫
  let ℓ : ℝ := (4*M*‖A x n‖^2+2*|D|+k*a0+4)/(4*a0^2)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hℓeq : 4*ℓ*a0^2=4*M*‖A x n‖^2+2*|D|+k*a0+4 := by
    dsimp [ℓ]
    field_simp
  let φ := planeBentWeight x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  refine ⟨ℓ,k,hℓ,?_,?_⟩
  · intro p
    have hh := plane_weight_center_gradient_bound hA hAs x n hn ℓ M hℓ.le hM p
    change -K*‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (b x)) p⟫ at hh
    have hhc := mul_le_mul_of_nonneg_left (hco p) hk.le
    have hprod : k*(m*‖p‖^2)=(K+1)*‖p‖^2 := by rw [← mul_assoc,hkm]
    rw [hprod] at hhc
    change ‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (b x)) p⟫+k*⟪p,A x p⟫
    nlinarith only [hh,hhc]
  · have haeq : a x=a0 := by
      change ⟪gradient (planeBentWeight x n ℓ M) x,
        A x (gradient (planeBentWeight x n ℓ M) x)⟫=⟪n,A x n⟫
      rw [planeBentWeight_gradient_center]
      simp only [map_neg,inner_neg_left,inner_neg_right,neg_neg]
    have hh := plane_weight_center_mass hA hAs x n ℓ M
    change ⟪gradient a x,b x⟫=2*ℓ*a0^2-2*M*‖A x n‖^2+D at hh
    change 3 < 2*⟪gradient a x,b x⟫-k*a x
    rw [haeq]
    have hD : -|D| ≤ D := neg_abs_le D
    nlinarith only [hh,hD,hℓeq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_local_carleman_weight {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ : ℝ,0 < ℓ ∧ ∃ k C r : ℝ,0 ≤ C ∧ 0 < r ∧
      let φ := planeBentWeight x n ℓ M
      let b : Plane → Plane := fun y ↦ A y (gradient φ y)
      let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
      (∀ y∈Metric.ball x r,∀ p : Plane,-k*⟪p,A y p⟫ ≤
        4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫) ∧
      (∀ y∈Metric.ball x r,2 ≤ 2*⟪gradient a y,b y⟫-k*a y) ∧
      (∀ y∈Metric.ball x r,sibling_planeElliptic A (planeDivergence b) y ≤ C) := by
  obtain ⟨ℓ,k,hℓ,hcenter,hmass0⟩ :=
    plane_weight_positive_center hA hAs x n hn hm hco M hM
  let φ := planeBentWeight x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := planeBentWeight_contDiff x n ℓ M
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := (plane_gradient_contDiff hφ).inner ℝ hb
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  let R : Plane → Plane →L[ℝ] Plane := fun y ↦
    (4 : ℝ) • ((fderiv ℝ b y).comp (A y))-(2 : ℝ) • (fderiv ℝ A y (b y))+k • A y
  have hcomp : Continuous (fun y : Plane ↦ (fderiv ℝ b y).comp (A y)) :=
    hdb.continuous.clm_comp hA.continuous
  have happ : Continuous (fun y : Plane ↦ fderiv ℝ A y (b y)) :=
    hdA.continuous.clm_apply hb.continuous
  have hs4 : Continuous (fun y : Plane ↦ (4 : ℝ) • ((fderiv ℝ b y).comp (A y))) :=
    hcomp.const_smul (4 : ℝ)
  have hs2 : Continuous (fun y : Plane ↦ (2 : ℝ) • fderiv ℝ A y (b y)) :=
    happ.const_smul (2 : ℝ)
  have hsk : Continuous (fun y : Plane ↦ k • A y) := hA.continuous.const_smul k
  have hR : Continuous R := (hs4.sub hs2).add hsk
  have hReq (y p : Plane) : ⟪p,R y p⟫=
      4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫+k*⟪p,A y p⟫ := by
    simp [R,inner_add_right,inner_sub_right,real_inner_smul_right]
  have hR0 (p : Plane) : ‖p‖^2 ≤ ⟪p,R x p⟫ := by
    rw [hReq]
    exact hcenter p
  have hRnear := plane_quadratic_coercive_near hR.continuousAt hR0
  have hmasscont : Continuous (fun y ↦ 2*⟪gradient a y,b y⟫-k*a y) :=
    (continuous_const.mul ((plane_gradient_contDiff ha).continuous.inner hb.continuous)).sub
      (continuous_const.mul ha.continuous)
  have hmassnear : ∀ᶠ y in 𝓝 x,2 ≤ 2*⟪gradient a y,b y⟫-k*a y :=
    (hmasscont.continuousAt.eventually (lt_mem_nhds (by linarith :
      2 < 2*⟪gradient a x,b x⟫-k*a x))).mono (fun _ hh ↦ hh.le)
  let c := sibling_planeElliptic A (planeDivergence b)
  have hc : Continuous c := (sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb)).continuous
  let C : ℝ := |c x|+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcnear : ∀ᶠ y in 𝓝 x,c y ≤ C :=
    (hc.continuousAt.eventually (gt_mem_nhds (by dsimp [C]; linarith [le_abs_self (c x)]))).mono
      (fun _ hh ↦ hh.le)
  have hall : ∀ᶠ y in 𝓝 x,
      (∀ p : Plane,0 ≤ ⟪p,R y p⟫) ∧ (2 ≤ 2*⟪gradient a y,b y⟫-k*a y) ∧ c y ≤ C := by
    filter_upwards [hRnear,hmassnear,hcnear] with y h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨r,hr,he⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ℓ,hℓ,k,C,r,hC,hr,?_,?_,?_⟩
  · intro y hy p
    have hh := (he (Metric.mem_ball.mp hy)).1 p
    rw [hReq] at hh
    linarith
  · intro y hy
    exact (he (Metric.mem_ball.mp hy)).2.1
  · intro y hy
    exact (he (Metric.mem_ball.mp hy)).2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeCarlemanG_contDiff {A : Plane → Plane →L[ℝ] Plane}
    {b : Plane → Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (planeCarlemanG A b f) := by
  have hp := plane_gradient_contDiff hf
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  exact (contDiff_const.mul (hp.inner ℝ (hdb.clm_apply (hA.clm_apply hp)))).sub
    (contDiff_const.mul (hp.inner ℝ ((hdA.clm_apply hb).clm_apply hp)))

lemma planeCarlemanG_compact {A : Plane → Plane →L[ℝ] Plane}
    {b : Plane → Plane} {f : Plane → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planeCarlemanG A b f) :=
  (compact_inner_left (plane_gradient_compact hc)).mul_left.sub
    (compact_inner_left (plane_gradient_compact hc)).mul_left

lemma plane_gradient_eq_zero_of_not_mem_tsupport {f : Plane → ℝ} {y : Plane}
    (hy : y∉tsupport f) : gradient f y=0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hh ↦ hy (plane_gradient_support hh)

lemma plane_carleman_integrated_identity {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) :
    (∫ y,(sibling_planeCarlemanP A b a τ f y)^2)=
      (∫ y,(sibling_planeCarlemanS A a τ f y)^2)+τ^2*(∫ y,(planeTransport b f y)^2)+
      τ*(∫ y,planeCarlemanG A b f y)+
      τ*(∫ y,(2*τ^2*⟪gradient a y,b y⟫-sibling_planeElliptic A (planeDivergence b) y)*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  have hi : Integrable (fun y ↦ ⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫) :=
    (hp.inner ℝ (hdb.clm_apply (hA.clm_apply hp))).continuous.integrable_of_hasCompactSupport
      (compact_inner_left (plane_gradient_compact hc))
  have hj : Integrable (fun y ↦ ⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫) :=
    (hp.inner ℝ ((hdA.clm_apply hb).clm_apply hp)).continuous.integrable_of_hasCompactSupport
      (compact_inner_left (plane_gradient_compact hc))
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hk : Integrable (fun y ↦ sibling_planeElliptic A (planeDivergence b) y*(f y)^2) :=
    ((sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb)).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hl : Integrable (fun y ↦ ⟪gradient a y,b y⟫*(f y)^2) :=
    (((plane_gradient_contDiff ha).inner ℝ hb).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  rw [plane_carleman_identity hA ha hb hf hc hAs τ]
  simp only [planeCarlemanG,sub_mul,mul_assoc]
  rw [integral_sub (hi.const_mul 4) (hj.const_mul 2),integral_sub ((hl.const_mul (τ^2)).const_mul 2) hk]
  simp only [integral_const_mul]
  ring

theorem plane_carleman_estimate {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane} {U : Set Plane} {k C τ : ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : tsupport f⊆U)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (hg : ∀ y∈U, ∀ p : Plane, -k*⟪p,A y p⟫≤
      4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫)
    (hm : ∀ y∈U,2≤2*⟪gradient a y,b y⟫-k*a y)
    (hC : 0≤C) (hbound : ∀ y∈U,sibling_planeElliptic A (planeDivergence b) y≤C)
    (hτ : 1≤τ) (hbig : C+k^2≤τ) :
    τ^3*(∫ y,(f y)^2)≤∫ y,(sibling_planeCarlemanP A b a τ f y)^2 := by
  have ht : 0≤τ := le_trans (by norm_num) hτ
  have hp := plane_gradient_contDiff hf
  have hE := hp.inner ℝ (hA.clm_apply hp)
  have hiE : Integrable (fun y ↦ ⟪gradient f y,A y (gradient f y)⟫) :=
    hE.continuous.integrable_of_hasCompactSupport (compact_inner_left (plane_gradient_compact hc))
  have hiG : Integrable (planeCarlemanG A b f) := (planeCarlemanG_contDiff hA hb hf).continuous.integrable_of_hasCompactSupport
    (planeCarlemanG_compact (A := A) (b := b) hc)
  have hge : -k*(∫ y,⟪gradient f y,A y (gradient f y)⟫)≤∫ y,planeCarlemanG A b f y := by
    rw [← integral_const_mul]
    apply integral_mono (hiE.const_mul (-k)) hiG
    intro y
    by_cases hy : y∈tsupport f
    · exact hg y (hs hy) (gradient f y)
    · simp [planeCarlemanG,plane_gradient_eq_zero_of_not_mem_tsupport hy]
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hiF : Integrable (fun y ↦ (f y)^2) := (hf.pow 2).continuous.integrable_of_hasCompactSupport hc2
  have hiAF : Integrable (fun y ↦ a y*(f y)^2) :=
    (ha.mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hS := planeCarlemanS_contDiff hA ha hf τ
  have hcS := planeCarlemanS_compact (A := A) (a := a) hc τ
  have hiSF : Integrable (fun y ↦ sibling_planeCarlemanS A a τ f y*f y) :=
    (hS.mul hf).continuous.integrable_of_hasCompactSupport hc.mul_left
  have hiSS : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2) :=
    (hS.pow 2).continuous.integrable_of_hasCompactSupport
      (hcS.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have he : (∫ y,⟪gradient f y,A y (gradient f y)⟫)=
      -(∫ y,sibling_planeCarlemanS A a τ f y*f y)+τ^2*(∫ y,a y*(f y)^2) := by
    have hL := planeElliptic_ibp hA hf hf hc
    have hiL : Integrable (fun y ↦ sibling_planeElliptic A f y*f y) :=
      ((sibling_planeElliptic_contDiff hA hf).mul hf).continuous.integrable_of_hasCompactSupport hc.mul_left
    have hh (y : Plane) : sibling_planeCarlemanS A a τ f y*f y=
        sibling_planeElliptic A f y*f y+τ^2*(a y*(f y)^2) := by dsimp [sibling_planeCarlemanS]; ring
    simp_rw [hh]
    rw [integral_add hiL (hiAF.const_mul (τ^2)),integral_const_mul,hL]
    ring
  let M : Plane → ℝ := fun y ↦ (2*τ^2*⟪gradient a y,b y⟫-
    sibling_planeElliptic A (planeDivergence b) y)*(f y)^2
  have hiM : Integrable M :=
    (((contDiff_const.mul ((plane_gradient_contDiff ha).inner ℝ hb)).sub
      (sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb))).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hme : (2*τ^2-C)*(∫ y,(f y)^2)+k*τ^2*(∫ y,a y*(f y)^2)≤∫ y,M y := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hiF.const_mul _) (hiAF.const_mul _)]
    apply integral_mono ((hiF.const_mul _).add (hiAF.const_mul _)) hiM
    intro y
    by_cases hy : y∈tsupport f
    · have hmy := mul_le_mul_of_nonneg_right (hm y (hs hy)) (sq_nonneg τ)
      have hby := hbound y (hs hy)
      have hcoeff : (2*τ^2-C)+k*τ^2*a y≤2*τ^2*⟪gradient a y,b y⟫-
          sibling_planeElliptic A (planeDivergence b) y := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (f y))
      dsimp [M]
      nlinarith
    · simp [M,image_eq_zero_of_notMem_tsupport hy]
  have hh : 0≤(∫ y,(sibling_planeCarlemanS A a τ f y)^2)+
      k*τ*(∫ y,sibling_planeCarlemanS A a τ f y*f y)+(k^2*τ^2/4)*(∫ y,(f y)^2) := by
    have hnon : 0≤∫ y,(sibling_planeCarlemanS A a τ f y+(k*τ/2)*f y)^2 := integral_nonneg (fun y ↦ sq_nonneg _)
    have hsplit (y : Plane) : (sibling_planeCarlemanS A a τ f y+(k*τ/2)*f y)^2=
        (sibling_planeCarlemanS A a τ f y)^2+k*τ*(sibling_planeCarlemanS A a τ f y*f y)+
        (k^2*τ^2/4)*(f y)^2 := by ring
    simp_rw [hsplit] at hnon
    have hisum : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+
        k*τ*(sibling_planeCarlemanS A a τ f y*f y)) := hiSS.add (hiSF.const_mul (k*τ))
    rw [integral_add hisum (hiF.const_mul (k^2*τ^2/4)),
      integral_add hiSS (hiSF.const_mul (k*τ))] at hnon
    simpa only [integral_const_mul] using hnon
  have hF0 : 0≤∫ y,(f y)^2 := integral_nonneg (fun y ↦ sq_nonneg _)
  have hTT : 0≤τ^2*(∫ y,(planeTransport b f y)^2) :=
    mul_nonneg (sq_nonneg τ) (integral_nonneg (fun y ↦ sq_nonneg _))
  have hcoeff : C*τ+k^2*τ^2/4≤τ^3 := by
    have hh1 := mul_le_mul_of_nonneg_left hτ hC
    have hh2 := mul_le_mul_of_nonneg_right hbig ht
    have hh3 := mul_le_mul_of_nonneg_right hh2 ht
    have hh4 := mul_nonneg (sq_nonneg k) (sq_nonneg τ)
    nlinarith
  have hcf := mul_le_mul_of_nonneg_right hcoeff hF0
  have hgτ := mul_le_mul_of_nonneg_left hge ht
  have hmτ := mul_le_mul_of_nonneg_left hme ht
  rw [he] at hgτ
  rw [plane_carleman_integrated_identity hA ha hb hf hc hAs τ]
  change _≤_+_+τ*(∫ y,M y)
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_weighted_carleman_near {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ : ℝ,0 < ℓ ∧ ∃ T r : ℝ,0 < r ∧
      ∀ (u : Plane → ℝ),ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      tsupport u⊆Metric.ball x r → ∀ τ : ℝ,T ≤ τ →
      τ^3*(∫ y,(Real.exp (τ*planeBentWeight x n ℓ M y)*u y)^2) ≤
        ∫ y,(Real.exp (τ*planeBentWeight x n ℓ M y)*sibling_planeElliptic A u y)^2 := by
  obtain ⟨ℓ,hℓ,k,C,r,hC,hr,hg,hmass,hbd⟩ :=
    plane_local_carleman_weight hA hAs x n hn hm hco M hM
  let φ := planeBentWeight x n ℓ M
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := planeBentWeight_contDiff x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := (plane_gradient_contDiff hφ).inner ℝ hb
  refine ⟨ℓ,hℓ,max 1 (C+k^2),r,hr,?_⟩
  intro u hu hc hs τ hτ
  let f : Plane → ℝ := fun y ↦ Real.exp (τ*φ y)*u y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_const.mul hφ).exp.mul hu
  have hfc : HasCompactSupport f := hc.mul_left
  have hfs : tsupport f⊆Metric.ball x r := tsupport_mul_subset_right.trans hs
  have hh := plane_carleman_estimate hA ha hb hf hfc hfs hAs hg hmass hC hbd
    ((le_max_left _ _).trans hτ) ((le_max_right _ _).trans hτ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with y
  rw [plane_elliptic_conjugation_forward hA hφ hu hAs]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SiblingCmcSecant
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

lemma planeBentWeight_outside_ball {a x n y : Plane} {R ℓ : ℝ}
    (hR : 0 < R) (hn : ‖n‖=1) (hx : x-a=R • n) (hℓ : 0 < ℓ)
    (hy : R ≤ ‖y-a‖) (hsmall : ℓ*‖y-x‖ ≤ 1) :
    planeBentWeight x n ℓ (4/R) y ≤  -(‖y-x‖^2/R) := by
  let s : ℝ := ⟪n,y-x⟫
  let q : ℝ := ‖y-x‖^2
  have hsq : R^2 ≤ ‖y-a‖^2 := by nlinarith [norm_nonneg (y-a)]
  have hid : ‖y-a‖^2=q+2*R*s+R^2 := by
    have he : y-a=(y-x)+R • n := by rw [← hx]; abel
    rw [he,norm_add_sq_real,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hn,mul_one,
      real_inner_smul_right]
    have hi : ⟪y-x,n⟫=⟪n,y-x⟫ := real_inner_comm _ _
    rw [hi]
    dsimp [s,q]
    ring
  have hb : -(q/(2*R)) ≤ s := by
    rw [← neg_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
    linarith
  have hsabs : |s| ≤ ‖y-x‖ := by
    simpa only [s,hn,one_mul] using abs_real_inner_le_norm n (y-x)
  have hls : ℓ*|s| ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hsabs hℓ.le) hsmall
  have hq : 0 ≤ q := sq_nonneg _
  rw [planeBentWeight_formula]
  change -s+(ℓ/2)*s^2-((4/R)/2)*q ≤  -(q/R)
  have hden : 0 < R := hR
  have hqr : 0 ≤ q/R := div_nonneg hq hR.le
  have hfour : (4/R)/2=2/R := by ring
  rw [hfour]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs] at hls
    have hh := mul_le_mul_of_nonneg_right hls hs
    have he : (2/R)*q=2*(q/R) := by ring
    rw [he]
    nlinarith
  · have hs' : s < 0 := lt_of_not_ge hs
    rw [abs_of_neg hs'] at hls
    have hh := mul_le_mul_of_nonneg_right hls (neg_nonneg.mpr hs'.le)
    have he : (2/R)*q=2*(q/R) := by ring
    have he' : q/(2*R)=(q/R)/2 := by ring
    rw [he'] at hb
    rw [he]
    nlinarith

lemma planeBentWeight_lower_near (x n : Plane) (ℓ M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ,0 < r ∧ ∀ y∈Metric.ball x r,-δ ≤ planeBentWeight x n ℓ M y := by
  have hh : ∀ᶠ y in 𝓝 x,-δ ≤ planeBentWeight x n ℓ M y :=
    ((planeBentWeight_contDiff x n ℓ M).continuous.continuousAt.eventually
      (lt_mem_nhds (by rw [planeBentWeight_center]; linarith :
        -δ < planeBentWeight x n ℓ M x))).mono (fun _ h ↦ h.le)
  obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp hh
  exact ⟨r,hr,fun y hy ↦ hh (Metric.mem_ball.mp hy)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_square_integrable {f : Plane → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun y ↦ (f y)^2) := by
  have hf2 : Continuous (fun y ↦ (f y)^2) := hf.pow 2
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by norm_num)
  exact hf2.integrable_of_hasCompactSupport hc2

lemma weighted_square_integrable {φ f : Plane → ℝ} (hφ : Continuous φ)
    (hf : Continuous f) (hc : HasCompactSupport f) (τ : ℝ) :
    Integrable (fun y ↦ (Real.exp (τ*φ y)*f y)^2) := by
  have hw : Continuous (fun y ↦ Real.exp (τ*φ y)*f y) :=
    (Real.continuous_exp.comp (continuous_const.mul hφ)).mul hf
  exact continuous_square_integrable hw hc.mul_left

lemma weighted_square_lower {φ f : Plane → ℝ} {W : Set Plane} {c τ : ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hW : MeasurableSet W) (ht : 0 ≤ τ) (hl : ∀ y∈W,c ≤ φ y) :
    (Real.exp (τ*c))^2*(∫ y in W,(f y)^2) ≤ ∫ y,(Real.exp (τ*φ y)*f y)^2 := by
  have hi : Integrable (fun y ↦ (f y)^2) :=
    continuous_square_integrable hf hc
  have hw := weighted_square_integrable hφ hf hc τ
  calc
    _=∫ y in W,(Real.exp (τ*c))^2*(f y)^2 := (integral_const_mul _ _).symm
    _≤∫ y in W,(Real.exp (τ*φ y)*f y)^2 := by
      apply integral_mono_ae ((hi.const_mul _).integrableOn) hw.integrableOn
      apply (ae_restrict_iff' hW).mpr
      exact ae_of_all _ (fun y hy ↦ by
        dsimp only
        rw [mul_pow]
        gcongr
        exact hl y hy)
    _≤_ := setIntegral_le_integral hw (ae_of_all _ (fun y ↦ sq_nonneg _))

lemma weighted_square_upper {φ e : Plane → ℝ} {c τ : ℝ}
    (hφ : Continuous φ) (he : Continuous e) (hc : HasCompactSupport e)
    (ht : 0 ≤ τ) (hb : ∀ y,e y≠0 → φ y ≤ c) :
    (∫ y,(Real.exp (τ*φ y)*e y)^2) ≤ (Real.exp (τ*c))^2*(∫ y,(e y)^2) := by
  have hi : Integrable (fun y ↦ (e y)^2) :=
    continuous_square_integrable he hc
  rw [← integral_const_mul]
  apply integral_mono (weighted_square_integrable hφ he hc τ) (hi.const_mul _)
  intro y
  by_cases hy : e y=0
  · simp [hy]
  · dsimp only
    rw [mul_pow]
    gcongr
    exact hb y hy

lemma carleman_polynomial_mass_zero {J E T : ℝ} (hJ : 0 ≤ J)
    (hbound : ∀ τ : ℝ,max 1 T ≤ τ → τ^3*J ≤ E) : J=0 := by
  by_contra hn
  have hp : 0 < J := lt_of_le_of_ne hJ (Ne.symm hn)
  let τ := max (max 1 T) (E/J+1)
  have hτ : max 1 T ≤ τ := le_max_left _ _
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτE : E/J+1 ≤ τ := le_max_right _ _
  have hcube : τ ≤ τ^3 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hτ1) (by linarith : 0 ≤ τ+1)
    have h2 := mul_nonneg h1 (by linarith : 0 ≤ τ)
    nlinarith only [h2]
  have hb := hbound τ hτ
  have hmul := mul_le_mul_of_nonneg_right hcube hJ
  have hfinal := mul_le_mul_of_nonneg_right hτE hJ
  have heq : (E/J+1)*J=E+J := by field_simp
  rw [heq] at hfinal
  linarith

theorem carleman_zero_on_open {φ f e : Plane → ℝ} {W : Set Plane} {c T : ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (he : Continuous e)
    (hfc : HasCompactSupport f) (hec : HasCompactSupport e) (hW : IsOpen W)
    (hl : ∀ y∈W,c ≤ φ y) (hb : ∀ y,e y≠0 → φ y ≤ c)
    (hest : ∀ τ : ℝ,T ≤ τ →
      τ^3*(∫ y,(Real.exp (τ*φ y)*f y)^2) ≤ ∫ y,(Real.exp (τ*φ y)*e y)^2) :
    ∀ y∈W,f y=0 := by
  let J := ∫ y in W,(f y)^2
  let E := ∫ y,(e y)^2
  have hJ : 0 ≤ J := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hz : J=0 := carleman_polynomial_mass_zero hJ (T := T) (by
    intro τ hτ
    have ht : 0 ≤ τ := le_trans (by norm_num) ((le_max_left _ _).trans hτ)
    have hlw := weighted_square_lower hφ hf hfc hW.measurableSet ht hl
    have huw := weighted_square_upper hφ he hec ht hb
    have hh := hest τ ((le_max_right _ _).trans hτ)
    have hm := mul_le_mul_of_nonneg_left hlw (pow_nonneg ht 3)
    have hpos : 0 < (Real.exp (τ*c))^2 := sq_pos_of_pos (Real.exp_pos _)
    apply (mul_le_mul_iff_right₀ hpos).mp
    change (Real.exp (τ*c))^2*(τ^3*J) ≤ (Real.exp (τ*c))^2*E
    nlinarith only [hm,hh,huw])
  have hi : Integrable (fun y ↦ (f y)^2) := continuous_square_integrable hf hfc
  have hae : (fun y ↦ (f y)^2)=ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _ ↦ sq_nonneg _)) hi.integrableOn).mp hz
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hW
    (hf.pow 2).continuousOn continuousOn_const
  intro y hy
  have hh := heq hy
  simpa only [Pi.zero_apply,pow_eq_zero_iff (by norm_num : (2 : ℕ)≠0)] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeElliptic_germ {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    {y : Plane} (he : f=ᶠ[𝓝 y] g) : sibling_planeElliptic A f y=sibling_planeElliptic A g y := by
  have hp : (fun z ↦ A z (gradient f z))=ᶠ[𝓝 y] (fun z ↦ A z (gradient g z)) :=
    he.gradient.mono (fun z hz ↦ congrArg (A z) hz)
  simp only [sibling_planeElliptic,planeDivergence,hp.fderiv_eq]

lemma sibling_planeElliptic_zero (A : Plane → Plane →L[ℝ] Plane) (y : Plane) :
    sibling_planeElliptic A (fun _ ↦ 0) y=0 := by
  simp [sibling_planeElliptic,planeDivergence,gradient_fun_const]

lemma planeElliptic_zero_on {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {O : Set Plane} (hO : IsOpen O) (hz : ∀ z∈O,f z=0) {y : Plane} (hy : y∈O) :
    sibling_planeElliptic A f y=0 := by
  have he : f=ᶠ[𝓝 y] (fun _ ↦ 0) := by
    filter_upwards [hO.mem_nhds hy] with z h
    exact hz z h
  rw [planeElliptic_germ he,sibling_planeElliptic_zero]

lemma planeElliptic_support {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ} :
    tsupport (sibling_planeElliptic A f)⊆tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hn
  have he0 : f=ᶠ[𝓝 y] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  have he := planeElliptic_germ (A := A) he0
  simp only [sibling_planeElliptic_zero] at he
  exact hy he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeBumpCutoff_eq {x : Plane} (b : ContDiffBump x) (u : Plane → ℝ)
    {y : Plane} (hy : y∈Metric.closedBall x b.rIn) : b y*u y=u y := by
  rw [b.one_of_mem_closedBall hy,one_mul]

lemma planeBumpCutoff_germ {x : Plane} (b : ContDiffBump x) (u : Plane → ℝ)
    {y : Plane} (hy : y∈Metric.ball x b.rIn) : (fun z ↦ b z*u z)=ᶠ[𝓝 y] u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
  exact planeBumpCutoff_eq b u (Metric.ball_subset_closedBall hz)

lemma planeBumpCutoff_error {A : Plane → Plane →L[ℝ] Plane} {x : Plane}
    (b : ContDiffBump x) (u : Plane → ℝ) {O : Set Plane} (hO : IsOpen O)
    (hz : ∀ z∈O,u z=0) (hLu : ∀ z∈Metric.ball x b.rIn,sibling_planeElliptic A u z=0)
    {y : Plane} (hy : sibling_planeElliptic A (fun z ↦ b z*u z) y≠0) :
    y∈Metric.closedBall x b.rOut ∧ y∉Metric.ball x b.rIn ∧ y∉O := by
  have hs : y∈tsupport (sibling_planeElliptic A (fun z ↦ b z*u z)) := subset_closure hy
  have hbs : y∈tsupport (fun z ↦ b z*u z) := planeElliptic_support hs
  refine ⟨?_,?_,?_⟩
  · have hh : y∈tsupport (b : Plane → ℝ) := tsupport_mul_subset_left hbs
    simpa only [b.tsupport_eq] using hh
  · intro hh
    apply hy
    rw [planeElliptic_germ (planeBumpCutoff_germ b u hh)]
    exact hLu y hh
  · intro hh
    apply hy
    exact planeElliptic_zero_on hO (fun z h ↦ by rw [hz z h,mul_zero]) hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_elliptic_zero_ball_extension {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ z v w,⟪v,A z w⟫=⟪w,A z v⟫)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {a x n : Plane} {R m s : ℝ} (hR : 0 < R) (hn : ‖n‖=1)
    (hx : x-a=R • n) (hm : 0 < m) (hs : 0 < s)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫)
    (hLu : ∀ y∈Metric.ball x s,sibling_planeElliptic A u y=0)
    (hzero : ∀ y∈Metric.ball a R,u y=0) :
    ∃ r : ℝ,0 < r ∧ ∀ y∈Metric.ball x r,u y=0 := by
  obtain ⟨ℓ,hℓ,T,r,hr,hcar⟩ := plane_weighted_carleman_near hA hAs x n hn hm hco
    (4/R) (by positivity)
  let ρ : ℝ := min (min (r/2) (s/2)) (1/(2*ℓ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r := (min_le_left _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith : r/2 < r))
  have hρs : ρ < s := (min_le_left _ _).trans_lt
    ((min_le_right _ _).trans_lt (by linarith : s/2 < s))
  have hρℓ : ℓ*ρ ≤ 1 := by
    have hh : ρ ≤ 1/(2*ℓ) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*ℓ)).mp hh
    have hlp : 0 ≤ ℓ*ρ := mul_nonneg hℓ.le hρ.le
    nlinarith
  let b : ContDiffBump x :=
    { rIn := ρ/2
      rOut := ρ
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let f : Plane → ℝ := fun y ↦ b y*u y
  let φ := planeBentWeight x n ℓ (4/R)
  let e := sibling_planeElliptic A f
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul hu
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_right
  have hfs : tsupport f⊆Metric.ball x r := by
    apply tsupport_mul_subset_left.trans
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hρr
  have he : ContDiff ℝ (⊤ : ℕ∞) e := sibling_planeElliptic_contDiff hA hf
  have hec : HasCompactSupport e := sibling_planeElliptic_compact hfc
  let δ : ℝ := (ρ/2)^2/R
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (by positivity)) hR
  have heb : ∀ y,e y≠0 → φ y ≤ -δ := by
    intro y hy
    obtain ⟨hyc,hyi,hyo⟩ := planeBumpCutoff_error b u Metric.isOpen_ball hzero
      (fun z hz ↦ hLu z ((Metric.ball_subset_ball (by dsimp [b]; linarith : b.rIn ≤ s)) hz)) hy
    have hyn : ‖y-x‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm,b] using hyc
    have hyi' : ρ/2 ≤ ‖y-x‖ := by
      simpa only [Metric.mem_ball,dist_eq_norm,b,not_lt] using hyi
    have hyo' : R ≤ ‖y-a‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hyo
    have hsmall : ℓ*‖y-x‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hyn hℓ.le).trans hρℓ
    have hbd := planeBentWeight_outside_ball hR hn hx hℓ hyo' hsmall
    have hq : δ ≤ ‖y-x‖^2/R := by
      dsimp [δ]
      gcongr
    exact hbd.trans (neg_le_neg hq)
  obtain ⟨r₁,hr₁,hlower⟩ := planeBentWeight_lower_near x n ℓ (4/R) hδ
  let r₂ := min r₁ (ρ/2)
  have hr₂ : 0 < r₂ := lt_min hr₁ (by positivity)
  have hz : ∀ y∈Metric.ball x r₂,f y=0 := carleman_zero_on_open
    (planeBentWeight_contDiff x n ℓ (4/R)).continuous hf.continuous he.continuous hfc hec
    Metric.isOpen_ball
    (fun y hy ↦ hlower y ((Metric.ball_subset_ball (min_le_left _ _)) hy)) heb
    (fun τ hτ ↦ hcar f hf hfc hfs τ hτ)
  refine ⟨r₂,hr₂,?_⟩
  intro y hy
  have hb1 : y∈Metric.closedBall x b.rIn :=
    Metric.ball_subset_closedBall ((Metric.ball_subset_ball (min_le_right r₁ (ρ/2))) hy)
  have heq := planeBumpCutoff_eq b u hb1
  exact heq.symm.trans (hz y hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_interior_tangent_ball_at {O : Set Plane} (hO : IsOpen O)
    {z : Plane} (hcl : z∈closure O) (hzero : z∉O) {s : ℝ} (hs : 0 < s) :
    ∃ a x : Plane,∃ R : ℝ,0 < R ∧ ‖x-a‖=R ∧ x∈closure O ∧ x∉O ∧
      Metric.ball a R⊆O ∧ Metric.closedBall a R⊆Metric.ball z s := by
  obtain ⟨a,ha,han⟩ := Metric.mem_closure_iff.mp hcl (s/4) (by positivity)
  have hnc : Oᶜ.Nonempty := ⟨z,hzero⟩
  let R := Metric.infDist a Oᶜ
  have hR : 0 < R := (hO.isClosed_compl.notMem_iff_infDist_pos hnc).mp (not_not.mpr ha)
  have hRa : R ≤ dist a z := Metric.infDist_le_dist_of_mem hzero
  have haN : dist a z < s/4 := by simpa only [dist_comm z a] using han
  obtain ⟨x,hx,hRx⟩ := hO.isClosed_compl.exists_infDist_eq_dist hnc a
  have hxR : ‖x-a‖=R := by simpa only [R,dist_comm a x,dist_eq_norm] using hRx.symm
  have hball : Metric.ball a R⊆O := Metric.ball_infDist_compl_subset
  have hxcl : x∈closure O := by
    apply closure_mono hball
    rw [closure_ball a hR.ne']
    simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]
  refine ⟨a,x,R,hR,hxR,hxcl,hx,hball,?_⟩
  intro y hy
  have hyn : dist y a ≤ R := hy
  have htri := dist_triangle y a z
  change dist y z < s
  linarith

theorem plane_elliptic_unique_continuation {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ z v w,⟪v,A z w⟫=⟪w,A z v⟫)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hpos : ∀ x∈Ω,∃ m : ℝ,0 < m ∧ ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫)
    (hLu : ∀ x∈Ω,sibling_planeElliptic A u x=0)
    (hzero : (Ω∩interior {x | u x=0}).Nonempty) : ∀ x∈Ω,u x=0 := by
  let O := Ω∩interior {x | u x=0}
  have hO : IsOpen O := hΩ.inter isOpen_interior
  have hsub : Ω⊆O := hc.subset_of_closure_inter_subset hO
    (by rcases hzero with ⟨x,hx⟩; exact ⟨x,hx.1,hx⟩) (by
      rintro z ⟨hzcl,hzΩ⟩
      by_contra hzO
      obtain ⟨s,hs,hsΩ⟩ := Metric.isOpen_iff.mp hΩ z hzΩ
      obtain ⟨a,x,R,hR,hxR,hxcl,hxO,hball,hclosed⟩ :=
        plane_interior_tangent_ball_at hO hzcl hzO hs
      have hxΩ : x∈Ω := hsΩ (hclosed (by
        simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]))
      obtain ⟨s₁,hs₁,hs₁Ω⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
      obtain ⟨m,hm,hco⟩ := hpos x hxΩ
      let n : Plane := R⁻¹ • (x-a)
      have hn : ‖n‖=1 := by simp only [n,norm_smul,Real.norm_eq_abs,abs_inv,
        abs_of_pos hR,hxR,inv_mul_cancel₀ hR.ne']
      have hxn : x-a=R • n := by simp only [n,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
      obtain ⟨r,hr,huz⟩ := plane_elliptic_zero_ball_extension hA hAs hu hR hn hxn hm hs₁
        hco (fun y hy ↦ hLu y (hs₁Ω hy)) (fun y hy ↦ show y∈{z | u z=0} from interior_subset (hball hy).2)
      apply hxO
      refine ⟨hxΩ,?_⟩
      exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
        (Metric.ball_mem_nhds x hr) huz))
  intro x hx
  exact show x∈{z | u z=0} from interior_subset (hsub hx).2

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalizedCMCCharts
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

lemma isOpenMap_quotientMap : IsOpenMap quotientMap := by
  have ho : IsOpenMap (Pi.map (fun _ : Fin 3 ↦ fun t : ℝ ↦ (t : AddCircle (1 : ℝ)))) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
      (Eventually.of_forall (fun _ ↦ QuotientAddGroup.mk_surjective))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ))).symm.isOpenMap.comp
    (ho.comp (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).isOpenMap)

lemma isOpenMap_shiftedQuotient (a : Cover) : IsOpenMap (fun v ↦ quotientMap (a+v)) :=
  isOpenMap_quotientMap.comp (Homeomorph.addLeft a).isOpenMap

lemma shiftedQuotient_nhds (a : Cover) :
    Filter.map (fun v ↦ quotientMap (a+v)) (𝓝 (0 : Cover))=𝓝 (quotientMap a) := by
  simpa only [add_zero] using (isOpenMap_shiftedQuotient a).map_nhds_eq
    ((continuous_quotientMap.comp (continuous_const.add continuous_id)).continuousAt (x := 0))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_strong_minimum {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hpb : ∀ y∈Ω,‖p y‖≤1) (hpos : ∀ y∈Ω,0≤f y)
    (hL : ∀ y∈Ω,planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0)
    {z : Plane} (hz : z∈Ω) (hfz : f z=0) : ∀ y∈Ω,f y=0 := by
  let O : Set Plane := Ω∩{x | 0<f x}
  have hO : IsOpen O := hΩ.inter (isOpen_lt continuous_const hf.continuous)
  by_cases hn : O.Nonempty
  · have hsub : Ω⊆O := hc.subset_of_closure_inter_subset hO
      (by obtain ⟨x,hx⟩ := hn; exact ⟨x,hx.1,hx⟩) (by
        rintro x ⟨hxcl,hxΩ⟩
        by_contra hxO
        obtain ⟨s,hs,hsΩ⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
        obtain ⟨a,b,R,hR,hbR,hbcl,hbO,hball,hclosed⟩ :=
          plane_interior_tangent_ball_at hO hxcl hxO hs
        have hbΩ : b∈Ω := hsΩ (hclosed (by
          simp only [Metric.mem_closedBall,dist_eq_norm,hbR,le_refl]))
        have hfb : f b=0 := le_antisymm (le_of_not_gt (fun hh ↦ hbO ⟨hbΩ,hh⟩)) (hpos b hbΩ)
        have hd := cmc_hopf_inward_derivative hp hf hR hbR hfb
          (fun y hy ↦ hpb y (hsΩ (hclosed hy)))
          (fun y hy ↦ (hball hy).2)
          (fun y hy ↦ hL y (hsΩ (hclosed (Metric.ball_subset_closedBall hy))))
        have hm : IsLocalMin f b := by
          filter_upwards [hΩ.mem_nhds hbΩ] with y hy
          rw [hfb]
          exact hpos y hy
        have hzero := hm.fderiv_eq_zero
        rw [hzero] at hd
        exact (lt_irrefl (0:ℝ)) hd)
    have hh := (hsub hz).2
    change 0<f z at hh
    rw [hfz] at hh
    exact (lt_irrefl (0:ℝ) hh).elim
  · intro y hy
    exact le_antisymm (le_of_not_gt (fun hh ↦ hn ⟨y,hy,hh⟩)) (hpos y hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma boundaryZeroGerm_open (S : Set Torus) (F : Torus → ℝ) :
    IsOpen (boundaryZeroGerm S F) := isOpen_setOfPred_eventually_nhds

lemma CenteredJacobiChart.zero_trace_germ
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (f : smoothPeriodicScalars)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),f.val (c.parameter y)=0) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  change ∀ᶠ x in 𝓝 (quotientMap cubeCenter),x∈frontier (openRepresentative E) →
    f.val (representative x)=0
  rw [←shiftedQuotient_nhds cubeCenter]
  change ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) →
    f.val (representative (quotientMap (cubeCenter+v)))=0
  have hP : Tendsto (normalPlaneCoordinates c.n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using ((normalPlaneCoordinates c.n).continuous.continuousAt (x := 0)).tendsto
  filter_upwards [c.cover_germ,hP.eventually hz] with v hv hzv hB
  rw [periodic_representative f.property.2]
  have he := hv.mp hB
  change f.val (cubeCenter+normalGraph c.n c.g (normalPlaneCoordinates c.n v))=0 at hzv
  rwa [he] at hzv

theorem CenteredJacobiChart.zero_germ_closed
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    (hcl : quotientMap cubeCenter∈closure (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)))) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  let A : Plane → Plane →L[ℝ] Plane := fun y ↦ cmcJacobian (gradient c.g y)
  let r := c.r/2
  have hr : 0 < r := half_pos c.r_pos
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := cmcJacobian_contDiff.comp (plane_gradient_contDiff c.smooth)
  have hL := c.classical_ground_state hE hμ hN hp haeN q f hjf hjw
  have hzero : (Metric.ball (0 : Plane) r∩interior {y | F y=0}).Nonempty := by
    have hc := c.closure_pullback inter_subset_left hcl hr
    obtain ⟨y,hy,hy0⟩ := Metric.mem_closure_iff.mp hc r hr
    refine ⟨y,hy.1,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hz := (continuous_quotientMap.comp c.parameter_smooth.continuous).continuousAt.eventually hy.2.2
    filter_upwards [hz,Metric.isOpen_ball.mem_nhds hy.1] with z hz hzball
    have hB := c.boundary_disk z (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by dsimp [r]; linarith [c.r_pos]) hzball))
    have he := hz hB
    simp only [Function.comp_apply,periodic_representative f.property.2] at he
    change c.weight z*f.val (c.parameter z)=0
    rw [he,mul_zero]
  have hz := plane_elliptic_unique_continuation hA
    (fun y v w ↦ (cmcJacobian_symmetric _ v w).trans (real_inner_comm _ _)) hF
    Metric.isOpen_ball (convex_ball (0 : Plane) r).isPreconnected
    (fun y hy ↦ ⟨1/8,by norm_num,fun v ↦ by
      have hs := (c.slope_disk y (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by dsimp [r]; linarith [c.r_pos]) hy))).trans (by norm_num : (1/4:ℝ)≤1)
      simpa only [A,real_inner_comm] using cmcJacobian_coercive hs v⟩)
    (fun y hy ↦ hL y hy) hzero
  apply c.zero_trace_germ f
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hr] with y hy
  have he := hz y hy
  exact (mul_eq_zero.mp he).resolve_left (cmcWeight_pos _).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarTranslate_gradient (a : Cover) (f : smoothPeriodicScalars) (x : Cover) :
    gradient (sibling_smoothScalarTranslate a f).val x=gradient f.val (x+a) := by
  have he : fderiv ℝ (sibling_smoothScalarTranslate a f).val x=fderiv ℝ f.val (x+a) := by
    have hd := (f.property.1.differentiable (by simp) (x+a)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const a)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,sibling_smoothScalarTranslate] using hd.fderiv
  simp only [gradient,he]

lemma normalTranslateJet_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    (u : SurfaceJet (μ.map (translateNormal a))) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (normalTranslateJet μ a u).1 z=u.1 (translateNormal a z) ∧
      (normalTranslateJet μ a u).2 z=u.2 (translateNormal a z) :=
  (Lp.coeFn_compMeasurePreserving u.1 (sibling_translateNormal_measurePreserving μ a)).and
    (Lp.coeFn_compMeasurePreserving u.2 (sibling_translateNormal_measurePreserving μ a))

lemma normalTranslateJet_smooth (μ : FiniteMeasure NormalBundle) (a : Cover)
    (f : smoothPeriodicScalars) :
    normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)=
      surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f) := by
  have hscalar := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  have hgrad := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hscalar,(smoothScalarValue (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.1]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).1 (translateNormal a z)=
      f.val (translateNormal a z).1 at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).1 z=f.val ((z.1 : Cover)+(-a)) at h₂
    rw [h₁,h₂,translateNormal_periodic_eval f.property.2]
    rfl
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hgrad,(smoothScalarGradient (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.2]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).2 (translateNormal a z)=
      smoothScalarGradient f (translateNormal a z) at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).2 z=
      smoothScalarGradient (sibling_smoothScalarTranslate (-a) f) z at h₂
    rw [h₁,h₂]
    change gradient f.val (translateNormal a z).1-
      ⟪(z.2 : Cover),gradient f.val (translateNormal a z).1⟫ • (z.2 : Cover)=_
    rw [translateNormal_periodic_eval (gradient_periodic f.property.2)]
    change _=gradient (sibling_smoothScalarTranslate (-a) f).val z.1-
      ⟪(z.2 : Cover),gradient (sibling_smoothScalarTranslate (-a) f).val z.1⟫ • (z.2 : Cover)
    rw [smoothScalarTranslate_gradient]
    rfl

lemma normalTranslateJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet (μ.map (translateNormal a))} (hu : u∈surfaceH1 (μ.map (translateNormal a))) :
    normalTranslateJet μ a u∈surfaceH1 μ := by
  have hc : IsClosed ((normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) :=
    (show IsClosed (surfaceH1 μ : Set (SurfaceJet μ)) from isClosed_closure).preimage
      (normalTranslateJet μ a).continuous
  apply closure_minimal (t := (normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) ?_ hc hu
  rintro _ ⟨f,rfl⟩
  change normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)∈surfaceH1 μ
  rw [normalTranslateJet_smooth]
  exact subset_closure (LinearMap.mem_range_self _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslate_multiplier (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u : Lp ℝ 2 (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)=
      surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u) := by
  apply Lp.ext
  have hm := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    (Lp.coeFn_lpSMul (r := 2) q' u)
  filter_upwards [Lp.coeFn_compMeasurePreserving (surfaceMultiplier _ q' u)
    (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_compMeasurePreserving u (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_lpSMul (r := 2) q (normalTranslatePullback μ a ℝ u),hm,hq] with z hz hu hv hm hq
  change (normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)) z=_ at hz
  change (normalTranslatePullback μ a ℝ u) z=_ at hu
  change (surfaceMultiplier _ q (normalTranslatePullback μ a ℝ u)) z=_ at hv
  change (surfaceMultiplier _ q' u) (translateNormal a z)=_ at hm
  rw [hz]
  simp only [Function.comp_apply]
  rw [hm,hv]
  simp only [smul_eq_mul,Pi.mul_apply,hq,hu,Function.comp_apply]

lemma normalTranslate_Jacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u v : SurfaceJet (μ.map (translateNormal a))) :
    surfaceJacobiB μ q (normalTranslateJet μ a u) (normalTranslateJet μ a v)=
      surfaceJacobiB (μ.map (translateNormal a)) q' u v := by
  change ⟪normalTranslatePullback μ a Cover u.2,normalTranslatePullback μ a Cover v.2⟫-
    ⟪surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u.1),
      normalTranslatePullback μ a ℝ v.1⟫=_
  rw [← normalTranslate_multiplier μ a q q' hq u.1,
    (normalTranslatePullback μ a Cover).inner_map_map,
    (normalTranslatePullback μ a ℝ).inner_map_map]
  rfl

lemma normalTranslateField_fderiv (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (x : Cover) :
    fderiv ℝ (normalTranslateField a N) x=fderiv ℝ N (x+a) := by
  have hd := (hN.differentiable (by simp) (x+a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const a)
  change fderiv ℝ (fun y : Cover ↦ N (y+a)) x=_
  simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hd.fderiv

lemma normalTranslate_curvature (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
        (normalTranslateField_smooth a hN) (translateNormal a z)=surfaceCurvatureLp μ N hN z := by
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq' := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous (normalTranslateField_smooth a hN)).comp
      (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ.map (translateNormal a) : Measure NormalBundle)
  have he := ae_of_ae_map (measurable_translateNormal a).aemeasurable hq'
  filter_upwards [hq,he] with z hz hz'
  change surfaceCurvatureLp μ N hN z=_ at hz
  change surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
    (normalTranslateField_smooth a hN) (translateNormal a z)=_ at hz'
  rw [hz,hz']
  change coverTrace ((fderiv ℝ (normalTranslateField a N) (translateNormal a z).1).comp
    (fderiv ℝ (normalTranslateField a N) (translateNormal a z).1))=
    coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  have hper := fderiv_periodic (normalTranslateField_periodic a hp)
  rw [translateNormal_periodic_eval hper,normalTranslateField_fderiv a hN]
  simp only [sub_add_cancel]

lemma normalTranslate_smooth_inverse (a : Cover) (f : smoothPeriodicScalars) :
    sibling_smoothScalarTranslate (-a) (sibling_smoothScalarTranslate a f)=f := by
  apply Subtype.ext
  funext x
  simp only [sibling_smoothScalarTranslate,neg_add_cancel_right]

lemma normalTranslate_directional (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x) (v : Cover) :
    directionalNormalScalar (normalTranslateField a N) (normalTranslateField_smooth a hN)
      (normalTranslateField_periodic a hp) v=sibling_smoothScalarTranslate a (directionalNormalScalar N hN hp v) := by
  apply Subtype.ext
  funext x
  change _=(directionalNormalScalar N hN hp v).val (x+a)
  rw [directionalNormalScalar_apply,directionalNormalScalar_apply]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslateField_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂(μ.map (translateNormal a) : Measure NormalBundle),
      normalTranslateField a N z.1=(z.2 : Cover) := by
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun ((hN.comp (continuous_id.add continuous_const)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change normalTranslateField a N (translateNormal a z).1=(z.2 : Cover)
  rw [translateNormal_periodic_eval (normalTranslateField_periodic a hp)]
  simpa only [normalTranslateField,sub_add_cancel] using hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarTranslate_descent (a : Cover) (f : smoothPeriodicScalars) (b : Torus) :
    (sibling_smoothScalarTranslate a f).val (representative b)=
      f.val (representative (b+quotientMap a)) := by
  have h := periodic_representative f.property.2 (representative b+a)
  rw [quotientMap_add,quotientMap_representative] at h
  exact h.symm

lemma normalTranslate_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    {u : SurfaceJet μ} (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {u' : SurfaceJet (μ.map (translateNormal a))} (he : normalTranslateJet μ a u'=u) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN)) u' v=0 := by
  intro v hv
  rw [← normalTranslate_Jacobi μ a _ _ (normalTranslate_curvature μ a hN hp),he]
  exact hju _ (normalTranslateJet_mem_surfaceH1 μ a hv)

lemma normalTranslate_smooth_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (f : smoothPeriodicScalars)
    (hj : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN))
      (surfaceSmoothJet _ (sibling_smoothScalarTranslate a f)) v=0 := by
  apply normalTranslate_weakJacobi μ a hN hp hj
  rw [normalTranslateJet_smooth,normalTranslate_smooth_inverse]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma preconnected_subset_of_relative_germ_closed {X : Type*} [TopologicalSpace X]
    {B O : Set X} (hB : IsPreconnected B) (hO : IsOpen O) (hne : (B∩O).Nonempty)
    (hc : closure (B∩O)∩B⊆O) : B⊆O := by
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  let U : Set B := Subtype.val ⁻¹' O
  have hUo : IsOpen U := hO.preimage continuous_subtype_val
  have hUc : IsClosed U := isClosed_of_closure_subset (by
    intro x hx
    have hx' : (x : X)∈closure (B∩O) := closure_mono
      (by rintro y ⟨z,hz,rfl⟩; exact ⟨z.property,hz⟩) (closure_subtype.mp hx)
    exact hc ⟨hx',x.property⟩)
  have hUn : U.Nonempty := by obtain ⟨x,hxB,hxO⟩ := hne; exact ⟨⟨x,hxB⟩,hxO⟩
  have he := (show IsClopen U from ⟨hUc,hUo⟩).eq_univ hUn
  intro x hx
  exact show (⟨x,hx⟩ : B)∈U by rw [he]; trivial

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingReflectNormal
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

lemma boundaryZeroGerm_homeomorph (e : Torus ≃ₜ Torus) (S : Set Torus) (F : Torus → ℝ) :
    boundaryZeroGerm (e ⁻¹' S) (F∘e)=e ⁻¹' boundaryZeroGerm S F := by
  ext x
  change (∀ᶠ y in 𝓝 x,e y∈S → F (e y)=0) ↔
    (∀ᶠ y in 𝓝 (e x),y∈S → F y=0)
  rw [←e.map_nhds_eq x]
  rfl

lemma boundaryZeroGerm_translation (a : Cover) (S : Set Torus) (f : smoothPeriodicScalars) :
    boundaryZeroGerm ((fun b ↦ b+quotientMap a) ⁻¹' S)
      (fun b ↦ (sibling_smoothScalarTranslate a f).val (representative b))=
      (fun b ↦ b+quotientMap a) ⁻¹' boundaryZeroGerm S (fun b ↦ f.val (representative b)) := by
  simp only [smoothScalarTranslate_descent]
  exact boundaryZeroGerm_homeomorph (Homeomorph.addRight (quotientMap a)) S
    (fun b ↦ f.val (representative b))

theorem isMinimizerAt_Jacobi_zero_germ_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    (x : Torus) (hx : x∈frontier (openRepresentative E))
    (hcl : x∈closure (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)))) :
    x∈boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)) := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  have hcl' : quotientMap cubeCenter∈closure (frontier (openRepresentative E')∩
      boundaryZeroGerm (frontier (openRepresentative E')) (fun b ↦ f'.val (representative b))) := by
    rw [hS',boundaryZeroGerm_translation,←preimage_inter]
    change quotientMap cubeCenter∈closure ((Homeomorph.addRight (quotientMap a)) ⁻¹' _)
    rw [←(Homeomorph.addRight (quotientMap a)).preimage_closure]
    change quotientMap cubeCenter+quotientMap a∈closure _
    rwa [hshift]
  have hz := c.zero_germ_closed hE' hμ' hN' hp' haeN' (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) (by
      rw [normalTranslate_directional a hN hp]
      exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)) hcl'
  rw [hS',boundaryZeroGerm_translation] at hz
  change quotientMap cubeCenter+quotientMap a∈boundaryZeroGerm _ _ at hz
  rwa [hshift] at hz

theorem isMinimizerAt_Jacobi_identity {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    (hpatch : (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x))).Nonempty) :
    ∀ x∈frontier (openRepresentative E),f.val (representative x)=0 := by
  have hsub := preconnected_subset_of_relative_germ_closed hconn (boundaryZeroGerm_open _ _) hpatch
    (fun x hx ↦ isMinimizerAt_Jacobi_zero_germ_closed hV hE hmin hμ hN hp haeN hjN f hjf x hx.2 hx.1)
  exact fun x hx ↦ (hsub hx).self_of_nhds hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CenteredJacobiChart.zero_germ_of_local_nonneg
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    (hpos : ∀ᶠ x in 𝓝 (quotientMap cubeCenter),x∈frontier (openRepresentative E) →
      0≤f.val (representative x))
    (hz : f.val cubeCenter=0) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  have hpos' : ∀ᶠ y in 𝓝 (0 : Plane),0≤f.val (c.parameter y) := by
    have ht : Tendsto (fun y ↦ quotientMap (c.parameter y)) (𝓝 (0 : Plane))
        (𝓝 (quotientMap cubeCenter)) := by
      have ht := (show Continuous (fun y : Plane ↦ quotientMap (c.parameter y)) from
        continuous_quotientMap.comp c.parameter_smooth.continuous).tendsto (0 : Plane)
      rw [c.parameter_zero] at ht
      exact ht
    filter_upwards [ht.eventually hpos,Metric.ball_mem_nhds (0 : Plane) c.r_pos] with y hy hr
    simpa only [periodic_representative f.property.2] using hy (c.boundary_disk y (Metric.ball_subset_closedBall hr))
  obtain ⟨s,hs,hsp⟩ := Metric.eventually_nhds_iff.mp hpos'
  let r := min s (c.r/2)
  have hr : 0 < r := lt_min hs (half_pos c.r_pos)
  have hrr : r ≤ c.r := (min_le_right _ _).trans (by linarith [c.r_pos])
  have hL := c.classical_ground_state hE hμ hN hp haeN q f hjf hjw
  have hzero := cmc_strong_minimum (plane_gradient_contDiff c.smooth) hF
    Metric.isOpen_ball (convex_ball (0 : Plane) r).isPreconnected
    (fun y hy ↦ (c.slope_disk y (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball hrr hy))).trans (by norm_num : (1/4:ℝ)≤1))
    (fun y hy ↦ mul_nonneg (cmcWeight_pos _).le (hsp (lt_of_lt_of_le hy (min_le_left _ _))))
    (fun y hy ↦ hL y (Metric.ball_subset_ball (min_le_right _ _) hy))
    (Metric.mem_ball_self hr) (show F 0=0 by simp [F,c.parameter_zero,hz])
  apply c.zero_trace_germ f
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hr] with y hy
  exact (mul_eq_zero.mp (hzero y hy)).resolve_left (cmcWeight_pos _).ne'

theorem isMinimizerAt_Jacobi_strong_minimum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    {x : Torus} (hx : x∈frontier (openRepresentative E))
    (hpos : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) → 0≤f.val (representative y))
    (hz : f.val (representative x)=0) :
    ∀ y∈frontier (openRepresentative E),f.val (representative y)=0 := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  have hpos' : ∀ᶠ b in 𝓝 (quotientMap cubeCenter),b∈frontier (openRepresentative E') →
      0≤f'.val (representative b) := by
    have ht : Tendsto (fun b : Torus ↦ b+quotientMap a) (𝓝 (quotientMap cubeCenter)) (𝓝 x) := by
      simpa only [hshift] using
        (show Continuous (fun b : Torus ↦ b+quotientMap a) from continuous_id.add continuous_const).continuousAt.tendsto (x := quotientMap cubeCenter)
    filter_upwards [ht.eventually hpos] with b hb hB
    rw [hS'] at hB
    simpa only [f',smoothScalarTranslate_descent] using hb hB
  have hz' : f'.val cubeCenter=0 := by
    have he := smoothScalarTranslate_descent a f (quotientMap cubeCenter)
    rw [periodic_representative f'.property.2,hshift] at he
    exact he.trans hz
  have hg := c.zero_germ_of_local_nonneg hE' hμ' hN' hp' haeN' (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) (by
      rw [normalTranslate_directional a hN hp]
      exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)) hpos' hz'
  rw [hS',boundaryZeroGerm_translation] at hg
  change quotientMap cubeCenter+quotientMap a∈boundaryZeroGerm _ _ at hg
  rw [hshift] at hg
  exact isMinimizerAt_Jacobi_identity hV hE hmin hconn hμ hN hp haeN hjN f hjf ⟨x,hx,hg⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N x=w := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [←quotientMap_add,show cubeCenter+a=x by dsimp [a]; abel]
    exact hx
  obtain ⟨w,hw⟩ := isMinimizerAt_center_normal_unique hV hE' hmin' hc
  refine ⟨w,?_⟩
  intro μ hμ N hN hp hae
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hh := hw (μ.map (translateNormal a)) (isNormalMeasure_translation hE hμ a)
    N' hN' hp' hae'
  change N (cubeCenter+a)=w at hh
  simpa only [show cubeCenter+a=x by dsimp [a]; abel] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FirstSeamFunction
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

lemma firstSeamFunction_contDiff : ContDiff ℝ (⊤ : ℕ∞) firstSeamFunction := by
  unfold firstSeamFunction
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ x 0) := (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).contDiff
  exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover ↦ 2*Real.pi)).mul hc).sin

lemma firstSeamFunction_periodic :
    ∀ n x,firstSeamFunction (x+latticeVector n)=firstSeamFunction x := by
  intro n x
  unfold firstSeamFunction
  simp only [PiLp.add_apply,latticeVector]
  convert Real.sin_add_int_mul_two_pi (2*Real.pi*x 0) (n 0) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingAxialProjection
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

theorem isMinimizerAt_normal_strong_minimum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) {x : Torus} (hx : x∈frontier (openRepresentative E))
    (hpos : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) → 0≤⟪v,N (representative y)⟫)
    (hz : ⟪v,N (representative x)⟫=0) :
    ∀ y∈frontier (openRepresentative E),⟪v,N (representative y)⟫=0 := by
  obtain ⟨ν,H,M,hM,hpM,hν,haM,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hE hmin
  have he : ∀ y∈frontier (openRepresentative E),N (representative y)=M (representative y) := by
    intro y hy
    obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin (representative y)
      (by simpa only [quotientMap_representative] using hy)
    exact (hw μ hμ N hN hp hae).trans (hw ν hν M hM hpM haM).symm
  have hjM := directionalNormalScalar_global_jacobi ν M hM hpM (fun i ↦ (hj i).2)
  have hzM : (directionalNormalScalar M hM hpM v).val (representative x)=0 := by
    rw [directionalNormalScalar_apply,←he x hx]
    exact hz
  have hpM' : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) →
      0≤(directionalNormalScalar M hM hpM v).val (representative y) := by
    filter_upwards [hpos] with y hy hyB
    rw [directionalNormalScalar_apply,←he y hyB]
    exact hy hyB
  have hzall := isMinimizerAt_Jacobi_strong_minimum hV hE hmin hc hν hM hpM haM hjM
    (directionalNormalScalar M hM hpM v) (hjM v) hx hpM' hzM
  intro y hy
  rw [he y hy]
  simpa only [directionalNormalScalar_apply] using hzall y hy

theorem isMinimizerAt_reflection_strict_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),N (representative x) 0=0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      N (representative x) 0<0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      0<N (representative x) 0) := by
  have hs := continuous_periodic_descent firstSeamFunction_contDiff.continuous firstSeamFunction_periodic
  by_cases hzero : ∀ x∈frontier (openRepresentative E),N (representative x) 0=0
  · exact Or.inl hzero
  · right
    rcases isMinimizerAt_reflection_weak_normal_sign hV hE hmin hc hR hμ hN hp hae with hneg|hpos
    · left
      intro x hx hxs
      refine lt_of_le_of_ne (hneg x hx hxs) ?_
      intro hzx
      have hzall := isMinimizerAt_normal_strong_minimum hV hE hmin hc hμ hN hp hae
        (-(EuclideanSpace.single 0 1)) hx (by
          filter_upwards [(isOpen_lt hs continuous_const).mem_nhds hxs] with y hy hyB
          simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_nonneg] using hneg y hyB hy)
        (by simp only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,hzx,neg_zero])
      apply hzero
      intro y hy
      simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_eq_zero] using hzall y hy
    · right
      intro x hx hxs
      refine lt_of_le_of_ne (hpos x hx hxs) ?_
      intro hzx
      have hzall := isMinimizerAt_normal_strong_minimum hV hE hmin hc hμ hN hp hae
        (EuclideanSpace.single 0 1) hx (by
          filter_upwards [(isOpen_lt hs continuous_const).mem_nhds hxs] with y hy hyB
          simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hpos y hyB hy)
        (by simp only [EuclideanSpace.inner_single_left,map_one,one_mul,←hzx])
      apply hzero
      intro y hy
      simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hzall y hy

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_TransverseTorus
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

lemma sibling_coverCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Cover) (i : Fin 3) :
    sibling_coverCoordinatePermute e x i=x (e i) := by
  rfl

lemma sibling_torusCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Torus) (i : Fin 3) :
    torusCoordinatePermute e x i=x (e i) := rfl

lemma coverCoordinatePermute_symm (e : Fin 3 ≃ Fin 3) :
    (sibling_coverCoordinatePermute e).symm=sibling_coverCoordinatePermute e.symm := by
  ext x : 1
  apply (sibling_coverCoordinatePermute e).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp only [sibling_coverCoordinatePermute_apply,Equiv.symm_apply_apply]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalMap
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
namespace LatticeIsometry

lemma volumeSupport_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    volumeSupport (e.torus ⁻¹' E)=e.torus ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (e.torus ⁻¹' E)∩Metric.ball a r=e.torus ⁻¹' (E∩Metric.ball (e.torus a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,e.torus.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,e.measurePreserving.measure_preimage
    (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    openRepresentative (e.torus ⁻¹' E)=e.torus ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [←preimage_compl,e.volumeSupport_preimage hE.compl]
  rfl

lemma frontier_openRepresentative_preimage (e : LatticeIsometry) {E : Set Torus}
    (hE : MeasurableSet E) :
    frontier (openRepresentative (e.torus ⁻¹' E))=e.torus ⁻¹' frontier (openRepresentative E) := by
  rw [e.openRepresentative_preimage hE]
  exact (e.torus.toHomeomorph.preimage_frontier _).symm

lemma measurable_normalMap (e : LatticeIsometry) : Measurable e.normalMap := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp (e.torus.continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact (e.cover.continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma normalMap_periodic_eval (e : LatticeIsometry) {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (z : NormalBundle) :
    F (e.normalMap z).1=F (e.cover z.1) := by
  change F (representative (e.torus (quotientMap z.1)))=_
  rw [←e.commute,periodic_representative hp]

lemma isNormalMeasure_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure (e.torus ⁻¹' E) (μ.map e.symm.normalMap) := by
  constructor
  · have hm : ((μ.map e.symm.normalMap).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply e.symm.measurable_normalMap
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,e.perimeter_eq hE.nullMeasurableSet]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map e.symm.normalMap (μ : Measure NormalBundle))=_
    rw [integral_map e.symm.measurable_normalMap.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      e.flux hF hE,←hμ.2 _ (e.symm.pullback_admissible hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪e.cover.symm (z.2 : Cover),F (e.symm.normalMap z).1⟫=
        ⟪(z.2 : Cover),e.cover (F (e.cover.symm z.1))⟫
      rw [e.symm.normalMap_periodic_eval hF.2.1]
      exact (e.cover.inner_map_map (e.cover.symm (z.2 : Cover)) (F (e.cover.symm z.1))).symm.trans
        (by rw [e.cover.apply_symm_apply])

lemma pullback_normal_ae (e : LatticeIsometry) {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map e.symm.normalMap) : Measure NormalBundle),e.pullback N z.1=(z.2 : Cover) := by
  rw [FiniteMeasure.toMeasure_map]
  have hc : Continuous (fun z : NormalBundle ↦ e.pullback N z.1) :=
    (e.pullback_contDiff hN).continuous.comp normalEmbedding_continuous.fst
  apply (ae_map_iff e.symm.measurable_normalMap.aemeasurable
    (isClosed_eq hc continuous_normalUnit).measurableSet).mpr
  filter_upwards [hae] with z hz
  change e.pullback N (e.symm.normalMap z).1=e.cover.symm (z.2 : Cover)
  rw [e.symm.normalMap_periodic_eval (e.pullback_periodic hp)]
  change e.cover.symm (N (e.cover (e.cover.symm z.1)))=_
  rw [e.cover.apply_symm_apply,hz]

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_torus_apply (i j : Fin 3) (x : Torus) :
    (axisReflection i).torus x j=if j=i then -x j else x j := by
  classical
  change (torusCoordinatePermute (Equiv.swap 0 i)
    (torusFirstReflection (torusCoordinatePermute (Equiv.swap 0 i) x))) j=_
  simp only [sibling_torusCoordinatePermute_apply,torusFirstReflection_apply,Equiv.swap_apply_self]
  by_cases h : j=i
  · subst j
    simp
  · have : Equiv.swap (0 : Fin 3) i j≠0 := by
      intro he
      have := congrArg (Equiv.swap (0 : Fin 3) i) he
      exact h (by simpa using this)
    simp [h,this]

lemma axisReflection_conjugate (i : Fin 3) (x : Torus) :
    (axisReflection i).torus (torusCoordinatePermute (Equiv.swap 0 i) x)=
      torusCoordinatePermute (Equiv.swap 0 i) (torusFirstReflection x) := by
  ext j
  simp only [axisReflection_torus_apply,sibling_torusCoordinatePermute_apply,torusFirstReflection_apply]
  have he : (j=i) ↔ Equiv.swap (0 : Fin 3) i j=0 := by
    constructor
    · rintro rfl; simp
    · intro h
      have hh := congrArg (Equiv.swap (0 : Fin 3) i) h
      simpa using hh
  simp only [he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusCoordinateSwap_involutive (i : Fin 3) :
    Function.Involutive (torusCoordinatePermute (Equiv.swap 0 i)) := by
  intro x
  ext j
  simp only [sibling_torusCoordinatePermute_apply,Equiv.swap_apply_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma representative_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Torus) :
    representative (torusCoordinatePermute e x)=sibling_coverCoordinatePermute e (representative x) := by
  ext j
  rfl

lemma LatticeIsometry.pullback_representative (e : LatticeIsometry) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (x : Torus) :
    e.pullback N (representative x)=e.cover.symm (N (representative (e.torus x))) := by
  have he := periodic_representative hp (e.cover (representative x))
  rw [e.commute,quotientMap_representative] at he
  change e.cover.symm (N (e.cover (representative x)))=_
  rw [he]

lemma coordinateSwap_pullback_scalar (i : Fin 3) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (x : Torus) :
    (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0=N (representative x) i := by
  rw [LatticeIsometry.pullback_representative _ hp]
  change (sibling_coverCoordinatePermute (Equiv.swap 0 i)).symm
    (N (representative (torusCoordinatePermute (Equiv.swap 0 i)
      (torusCoordinatePermute (Equiv.swap 0 i) x)))) 0=_
  rw [torusCoordinateSwap_involutive,coverCoordinatePermute_symm]
  simp only [sibling_coverCoordinatePermute_apply,Equiv.symm_swap,Equiv.swap_apply_left]

theorem isMinimizerAt_axis_strict_normal_sign_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),N (representative x) i=0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      N (representative x) i<0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      0<N (representative x) i) := by
  let e := coordinatePermutation (Equiv.swap 0 i)
  let F := e.torus ⁻¹' E
  have hF : MeasurableSet F := hE.preimage e.torus.continuous.measurable
  have hmF : IsMinimizerAt V F := e.isMinimizerAt hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    change IsPreconnected (frontier (openRepresentative (e.torus ⁻¹' E)))
    rw [e.frontier_openRepresentative_preimage hE]
    exact e.torus.toHomeomorph.isPreconnected_preimage.mpr hc
  have hRF : F=ᵐ[torusVolume](torusFirstReflection ⁻¹' F) := by
    have hh := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq hR
    filter_upwards [hh] with x hx
    change (e.torus x∈E)=((axisReflection i).torus (e.torus x)∈E) at hx
    change (e.torus x∈E)=(e.torus (torusFirstReflection x)∈E)
    change (torusCoordinatePermute (Equiv.swap 0 i) x∈E)=
      ((axisReflection i).torus (torusCoordinatePermute (Equiv.swap 0 i) x)∈E) at hx
    rwa [axisReflection_conjugate] at hx
  have hpoint (x : Torus) (hx : x∈frontier (openRepresentative E)) :
      e.torus x∈frontier (openRepresentative F) := by
    change e.torus x∈frontier (openRepresentative (e.torus ⁻¹' E))
    rw [e.frontier_openRepresentative_preimage hE]
    change e.torus (e.torus x)∈frontier (openRepresentative E)
    change torusCoordinatePermute (Equiv.swap 0 i)
      (torusCoordinatePermute (Equiv.swap 0 i) x)∈frontier (openRepresentative E)
    rwa [torusCoordinateSwap_involutive]
  have hseam (x : Torus) : firstSeamFunction (representative (e.torus x))=
      Real.sin (2*Real.pi*representative x i) := by
    change Real.sin (2*Real.pi*representative (torusCoordinatePermute (Equiv.swap 0 i) x) 0)=_
    rw [representative_coordinatePermute,sibling_coverCoordinatePermute_apply,Equiv.swap_apply_left]
  rcases isMinimizerAt_reflection_strict_normal_sign hV hF hmF hcF hRF
    (e.isNormalMeasure_preimage hE hμ) (e.pullback_contDiff hN) (e.pullback_periodic hp)
    (e.pullback_normal_ae hN hp hae) with hz|hn|hpos
  · left
    intro x hx
    have hh := hz (e.torus x) (hpoint x hx)
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0=0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; left
    intro x hx hs
    have hh := hn (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0<0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; right
    intro x hx hs
    have hh := hpos (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change 0<(coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign_oai := @OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign_oai
