-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_nodal_splice_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:16:05.378356+00:00
-- url     : https://prove2.me/submissions/bf02ce17-59c4-4610-824c-61c5f08e6557

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_linear_chart
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_smooth_CMC
import Theorems.Thm_OAI_CubicTorus_normalMeasure_H1_jacobi_signed_graph_smoothAt

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
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
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

lemma integral_mul_eq_restrict_of_tsupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    (f q : X → ℝ) (hq : tsupport q ⊆ K) :
    (∫ x, f x * q x ∂μ) = ∫ x in K, f x * q x ∂μ := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change f x * q x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hq h)), mul_zero]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
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

lemma graphSmooth_affine (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e : ℝ) (x : Plane) :
    m+e*graphSmooth b f x = ∫ y, (m+e*f (x-y)) ∂graphSmoothingMeasure b := by
  rw [integral_add (integrable_const _) ((graphSmooth_integrable b hf x).const_mul e),
    integral_const_mul]
  simp [graphSmooth]

lemma graphSmooth_affine_abs_le (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e H : ℝ)
    (hH : ∀ y, |m+e*f y| ≤ H) (x : Plane) : |m+e*graphSmooth b f x| ≤ H := by
  rw [graphSmooth_affine b hf]
  calc
    _ ≤ ∫ y, |m+e*f (x-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, H ∂graphSmoothingMeasure b := by
      apply integral_mono ((integrable_const m).add ((graphSmooth_integrable b hf x).const_mul e)).norm
        (integrable_const _)
      exact fun y ↦ hH _
    _ = _ := by simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
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

lemma second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0≤deriv (deriv f) t := by
  by_contra hn
  have hn' : deriv (deriv f) t<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn' hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ ↦ f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

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

lemma cmcWeight_ge_one (p : Plane) : 1 ≤ cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]
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

lemma cmcJacobian_norm_le {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcJacobian p v‖≤2*‖v‖ := by
  have hs := cmcWeight_ge_one p
  have hs0 := cmcWeight_pos p
  have hsi : (cmcWeight p)⁻¹≤1 := inv_le_one₀ hs0 |>.mpr hs
  have hs3 : ((cmcWeight p)^3)⁻¹≤1 := by
    apply (inv_le_one₀ (by positivity : 0<(cmcWeight p)^3)).mpr
    nlinarith [sq_nonneg (cmcWeight p-1)]
  rw [cmcJacobian_apply]
  calc
    _ ≤ ‖(cmcWeight p)⁻¹ • v‖ + ‖(((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = (cmcWeight p)⁻¹*‖v‖+((cmcWeight p)^3)⁻¹*|⟪p,v⟫| *‖p‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr hs0.le),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs0.le 3))]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) hsi
      · apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hs3) (norm_nonneg _)).trans
        apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
          (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

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

lemma exists_plane_test_cutoff {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ b : ContDiffBump (0 : Plane), b.rOut<R ∧ ∀ y, b y*ψ y=ψ y := by
  obtain ⟨s,hsR,hsb⟩ := exists_lt_subset_ball isClosed_closure hs
  let t := max (R/2) s
  have ht : 0<t := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have htR : t<R := max_lt (by linarith) hsR
  let b : ContDiffBump (0 : Plane) := ⟨t,(t+R)/2,ht,by linarith⟩
  refine ⟨b,by change (t+R)/2<R; linarith,fun y ↦ ?_⟩
  by_cases hy : ψ y=0
  · rw [hy,mul_zero]
  · have hym : y∈Metric.closedBall (0 : Plane) b.rIn :=
      Metric.ball_subset_closedBall ((Metric.ball_subset_ball (le_max_right _ _))
        (hsb (subset_tsupport ψ hy)))
    rw [b.one_of_mem_closedBall hym,one_mul]

theorem exists_C1_test_approximants {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ (f : ℕ → Plane → ℝ) (K : Set Plane) (M : ℝ), IsCompact K ∧
      K⊆Metric.ball 0 R ∧ 0≤M ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) ∧ tsupport (f i)⊆K) ∧
      (∀ i y, ‖f i y‖≤M ∧ ‖fderiv ℝ (f i) y‖≤M) ∧
      (∀ y, Tendsto (fun i ↦ f i y) atTop (𝓝 (ψ y))) ∧
      (∀ y, Tendsto (fun i ↦ fderiv ℝ (f i) y) atTop (𝓝 (fderiv ℝ ψ y))) := by
  obtain ⟨b,hbR,hbψ⟩ := exists_plane_test_cutoff hR hs
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  obtain ⟨Lb,hLb⟩ := hbc.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (by simp)
  obtain ⟨C,hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hCb (y : Plane) : ‖ψ y‖≤C := hC (mem_range_self y)
  have hC0 : 0≤C := (norm_nonneg (ψ 0)).trans (hCb 0)
  let f (i : ℕ) : Plane → ℝ := fun y ↦ b y*graphSmooth (graphMollifier i) ψ y
  have hfs (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f i) := b.contDiff.mul (graphSmooth_contDiff _ hL)
  have hsm (i : ℕ) (y : Plane) : ‖graphSmooth (graphMollifier i) ψ y‖≤C := by
    simpa only [zero_add,one_mul,Real.norm_eq_abs] using
      graphSmooth_affine_abs_le (graphMollifier i) hL 0 1 C (by simpa only [zero_add,one_mul,Real.norm_eq_abs] using hCb) y
  have hb1 (y : Plane) : ‖b y‖≤1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg b.nonneg] using b.le_one (x := y)
  have hdf (i : ℕ) (y : Plane) : fderiv ℝ (f i) y =
      b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y +
      graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y := by
    exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
      ((graphSmooth_contDiff _ hL).differentiable (by simp)).differentiableAt
  refine ⟨f,tsupport b,C+(L:ℝ)+C*(Lb:ℝ),b.hasCompactSupport,?_,by positivity,
    fun i ↦ ⟨hfs i,tsupport_mul_subset_left⟩,?_,?_,?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hbR
  · intro i y
    constructor
    · have hh : ‖f i y‖≤C := by
        change ‖b y*graphSmooth (graphMollifier i) ψ y‖≤C
        rw [norm_mul]
        exact (mul_le_mul (hb1 y) (hsm i y) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      nlinarith [Lb.coe_nonneg,L.coe_nonneg]
    · rw [hdf]
      calc
        _ ≤ ‖b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y‖+
            ‖graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y‖ := norm_add_le _ _
        _ ≤ (L:ℝ)+C*(Lb:ℝ) := by
          simp only [norm_smul]
          apply add_le_add
          · exact (mul_le_mul (hb1 y) (norm_fderiv_le_of_lipschitz ℝ (graphSmooth_lipschitz _ hL))
              (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
          · exact mul_le_mul (hsm i y) (norm_fderiv_le_of_lipschitz ℝ hLb) (norm_nonneg _) hC0
        _ ≤ _ := by linarith
  · intro y
    simpa only [hbψ y] using (graphSmooth_tendsto hL y).const_mul (b y)
  · intro y
    have he : (fun y ↦ b y*ψ y)=ψ := funext hbψ
    have hdp : fderiv ℝ ψ y=b y • fderiv ℝ ψ y+ψ y • fderiv ℝ b y := by
      conv_lhs => rw [← he]
      exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
        (hψ.differentiable (by simp)).differentiableAt
    rw [hdp]
    simpa only [hdf] using
      ((graphSmooth_fderiv_tendsto hL (hψ.continuous_fderiv (by simp)).continuousAt).const_smul (b y)).add
        ((graphSmooth_tendsto hL y).smul_const (fderiv ℝ b y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcFlux_norm_le (p : Plane) : ‖cmcFlux p‖≤‖p‖ := by
  change ‖(cmcWeight p)⁻¹ • p‖≤‖p‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (cmcWeight_pos p).le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (cmcWeight_pos p)).mpr (cmcWeight_ge_one p))

lemma cmcFlux_difference_bound {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    ‖cmcFlux q-cmcFlux p‖≤2*‖q-p‖ := by
  apply (convex_closedBall (0 : Plane) (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ (cmcFlux_hasFDerivAt x).differentiableAt) ?_
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq)
  intro x hx
  rw [(cmcFlux_hasFDerivAt x).fderiv]
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (cmcJacobian_norm_le (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

lemma cmcFlux_line_deriv (p q : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ⟪q-p,cmcFlux (p+s • (q-p))⟫)
      ⟪q-p,cmcJacobian (p+t • (q-p)) (q-p)⟫ t := by
  have hl : HasDerivAt (fun s : ℝ ↦ p+s • (q-p)) (q-p) t := by
    simpa using ((hasDerivAt_id t).smul_const (q-p)).const_add p
  have hh := (hasDerivAt_const t (q-p)).inner ℝ ((cmcFlux_hasFDerivAt _).comp_hasDerivAt t hl)
  simpa [Function.comp_def] using hh

lemma cmcFlux_strong_monotone {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    (1/8)*‖q-p‖^2≤⟪q-p,cmcFlux q-cmcFlux p⟫ := by
  let f : ℝ → ℝ := fun t ↦ ⟪q-p,cmcFlux (p+t • (q-p))⟫
  have hf : Differentiable ℝ f := fun t ↦ (cmcFlux_line_deriv p q t).differentiableAt
  have hb (t : ℝ) (ht : t∈interior (Icc (0:ℝ) 1)) :
      (1/8)*‖q-p‖^2≤deriv f t := by
    rw [(cmcFlux_line_deriv p q t).deriv]
    apply cmcJacobian_coercive
    have htt := interior_subset ht
    have he : p+(q-p)=q := by abel
    have hh := (convex_closedBall (0 : Plane) (1 : ℝ)).add_smul_mem (x := p) (y := q-p)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
      (by simpa only [he,Metric.mem_closedBall,dist_zero_right] using hq) htt
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh
  have hh := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn hb 0 (by norm_num) 1 (by norm_num) (by norm_num)
  have he : p+(q-p)=q := by abel
  simpa only [f,sub_zero,mul_one,one_smul,zero_smul,add_zero,he,inner_sub_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_cmc_gradient (g : Plane → ℝ) : Measurable (fun y ↦ cmcFlux (gradient g y)) :=
  cmcFlux_contDiff.continuous.measurable.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g))

lemma measurable_differential_apply {F : Plane → Plane} (hF : Measurable F) (ψ : Plane → ℝ) :
    Measurable (fun y ↦ fderiv ℝ ψ y (F y)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((measurable_fderiv ℝ ψ).prodMk hF)

theorem weak_flux_C1_test {R : ℝ} (hR : 0<R) {F : Plane → Plane}
    (hF : Measurable F) {N : ℝ} (hN : ∀ y, ‖F y‖≤N) (A : ℝ)
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ⊆Metric.ball 0 R → (∫ y, fderiv ℝ φ y (F y))=A*(∫ y, φ y))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y (F y))=A*(∫ y, ψ y) := by
  obtain ⟨f,K,M,hK,hKR,hM,hf,hb,ht,hdt⟩ := exists_C1_test_approximants hR hψ hc hs
  have hN0 : 0≤N := (norm_nonneg (F 0)).trans (hN 0)
  let B : Plane → ℝ := K.indicator (fun _ ↦ M*N)
  let C : Plane → ℝ := K.indicator (fun _ ↦ M)
  have hBi : Integrable B := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hCi : Integrable C := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have htd : Tendsto (fun i ↦ ∫ y, fderiv ℝ (f i) y (F y)) atTop
      (𝓝 (∫ y, fderiv ℝ ψ y (F y))) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun _ ↦ (measurable_differential_apply hF _).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show B y=M*N from indicator_of_mem hy _]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hb i y).2 (hN y) (norm_nonneg _) hM)
      · have hz := fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,zero_apply,norm_zero,show B y=0 from indicator_of_notMem hy _]
    · apply Eventually.of_forall
      intro y
      exact ((show Continuous (fun L : Plane →L[ℝ] ℝ ↦ L (F y)) from
        continuous_id.clm_apply continuous_const).tendsto _).comp (hdt y)
  have htv : Tendsto (fun i ↦ ∫ y, f i y) atTop (𝓝 (∫ y, ψ y)) := by
    apply tendsto_integral_of_dominated_convergence C
      (fun i ↦ (hf i).1.continuous.aestronglyMeasurable) hCi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show C y=M from indicator_of_mem hy _]
        exact (hb i y).1
      · have hz : f i y=0 := image_eq_zero_of_notMem_tsupport (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,norm_zero,show C y=0 from indicator_of_notMem hy _]
    · exact Eventually.of_forall ht
  have he (i : ℕ) : (∫ y, fderiv ℝ (f i) y (F y))=A*(∫ y, f i y) :=
    hw (f i) (hf i).1 (hK.of_isClosed_subset isClosed_closure (hf i).2) ((hf i).2.trans hKR)
  exact tendsto_nhds_unique htd (by simpa only [he] using htv.const_mul A)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_differential_apply_of_bounded {F : Plane → Plane} (hF : Measurable F)
    {N : ℝ} (hN : ∀ y, ‖F y‖≤N) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun y ↦ fderiv ℝ ψ y (F y)) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hi := (integrableOn_const (μ := (volume : Measure Plane)) (C := (L:ℝ)*N) hc.measure_lt_top.ne).integrable_indicator
    isClosed_closure.measurableSet
  apply hi.mono' (measurable_differential_apply hF ψ).aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈tsupport ψ
  · rw [indicator_of_mem hy]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hN y) (norm_nonneg _) L.coe_nonneg)
  · rw [indicator_of_notMem hy,fderiv_of_notMem_tsupport ℝ hy,zero_apply,norm_zero]

lemma translated_test_support {R r : ℝ} {ψ : Plane → ℝ} {a : Plane}
    (hs : tsupport ψ⊆Metric.ball 0 r) (ha : r+‖a‖≤R) :
    tsupport (fun y ↦ ψ (y-a))⊆Metric.ball 0 R := by
  intro y hy
  have hys := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun y : Plane ↦ y-a)) hy)
  have hh : ‖y-a‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hys
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖y‖ = ‖(y-a)+a‖ := by rw [sub_add_cancel]
    _ ≤ ‖y-a‖+‖a‖ := norm_add_le _ _
    _ < r+‖a‖ := by linarith
    _ ≤ R := ha

lemma WeakCMCGraph.translated_test {g : Plane → ℝ} {H R r : ℝ}
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))))=H*(∫ y, ψ y) := by
  let φ : Plane → ℝ := fun y ↦ ψ (y-a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.sub contDiff_const)
  have hφs := translated_test_support hs ha
  have hφc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) R).of_isClosed_subset
    isClosed_closure (hφs.trans Metric.ball_subset_closedBall)
  have he := hw φ hφ hφc hφs
  have hd := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ φ y (cmcFlux (gradient g y))) a
  have hv := integral_add_right_eq_self (μ := (volume : Measure Plane)) φ a
  simp only [φ,fderiv_comp_sub,add_sub_cancel_right] at hd hv
  simp only [φ,fderiv_comp_sub] at he
  rw [hd,he,← hv]

theorem WeakCMCGraph.difference_test {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {H R r : ℝ} (hr : 0 < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0 := by
  have hF := measurable_cmc_gradient g
  have hb (y : Plane) : ‖cmcFlux (gradient g y)‖≤(K:ℝ) := by
    exact (cmcFlux_norm_le _).trans (by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg)
  have hFm : Measurable (fun y ↦ cmcFlux (gradient g (y+a))) :=
    hF.comp (measurable_id.add_const a)
  have hDb (y : Plane) : ‖cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)‖≤2*(K:ℝ) :=
    (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])
  apply weak_flux_C1_test hr (hFm.sub hF) hDb 0 ?_ hψ hc hs |>.trans (by simp)
  intro φ hφ hφc hφs
  change (∫ y, fderiv ℝ φ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0*(∫ y, φ y)
  simp_rw [map_sub]
  rw [integral_sub
    (integrable_differential_apply_of_bounded hFm (fun y ↦ hb (y+a)) (hφ.of_le (by simp)) hφc)
    (integrable_differential_apply_of_bounded hF hb (hφ.of_le (by simp)) hφc)]
  rw [hw.translated_test ha hφ hφs,hw φ hφ hφc (hφs.trans (Metric.ball_subset_ball ?_))]
  · simp
  · linarith [norm_nonneg a]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_C1_cutoff_product {U : Set Plane} (hU : IsOpen U)
    {η w : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hw : ContDiffOn ℝ 1 w U)
    (hs : tsupport η⊆U) : ContDiff ℝ 1 (fun y ↦ η y^2*w y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact (hη.contDiffAt.pow 2).mul ((hw y (hs hy)).contDiffAt (hU.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma energyTest_tsupport {η w : Plane → ℝ} : tsupport (fun y ↦ η y^2*w y)⊆tsupport η := by
  apply closure_mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  simp [hy]

lemma integrable_bounded_compact {f : Plane → ℝ} (hf : Measurable f)
    {K : Set Plane} (hK : IsCompact K) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    (hz : ∀ y, y∉K → f y=0) : Integrable f := by
  have hi : Integrable (K.indicator (fun _ : Plane ↦ M)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈K
  · rw [indicator_of_mem hy]; exact hb y
  · rw [indicator_of_notMem hy,hz y hy,norm_zero]

lemma cmc_energy_absorption {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1)
    (a w : ℝ) (L : Plane →L[ℝ] ℝ) :
    (1/16)*a^2*‖q-p‖^2-64*w^2*‖L‖^2 ≤
      a^2*⟪q-p,cmcFlux q-cmcFlux p⟫+2*a*w*L (cmcFlux q-cmcFlux p) := by
  let d := ‖q-p‖
  let F := cmcFlux q-cmcFlux p
  have hc : (1/8)*d^2 ≤ ⟪q-p,F⟫ := cmcFlux_strong_monotone hp hq
  have hF : ‖F‖≤2*d := cmcFlux_difference_bound hp hq
  have hL : |L F|≤2*‖L‖*d := by
    exact (ContinuousLinearMap.le_opNorm L F).trans (by nlinarith [norm_nonneg L])
  have he : |2*a*w*L F|≤4*|a| *|w| *‖L‖*d := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤2*|a| *|w| by positivity)
    nlinarith
  have hn : -(4*|a| *|w| *‖L‖*d)≤2*a*w*L F := (neg_le_neg he).trans (neg_abs_le _)
  have hca := mul_le_mul_of_nonneg_left hc (sq_nonneg a)
  have hs := sq_nonneg (|a| *d/4-8*|w| *‖L‖)
  have ha2 := sq_abs a
  have hw2 := sq_abs w
  change (1/16)*a^2*d^2-64*w^2*‖L‖^2 ≤ a^2*⟪q-p,F⟫+2*a*w*L F
  nlinarith

lemma translated_difference_contDiffOn {g : Plane → ℝ} {R r : ℝ} {a : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R) :
    ContDiffOn ℝ 1 (fun y ↦ g (y+a)-g y) (Metric.ball 0 r) := by
  apply (hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_).sub
    (hg.mono (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  intro y hy
  rw [Metric.mem_ball,dist_zero_right]
  have hy' : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  change ‖y+a‖<R
  exact (norm_add_le _ _).trans_lt (by linarith)

lemma translated_difference_fderiv {g : Plane → ℝ} {R r : ℝ} {a y : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R)
    (hy : y∈Metric.ball 0 r) (v : Plane) :
    fderiv ℝ (fun y ↦ g (y+a)-g y) y v=⟪gradient g (y+a)-gradient g y,v⟫ := by
  have hy0 : y∈Metric.ball (0 : Plane) R := Metric.ball_subset_ball (by linarith [norm_nonneg a]) hy
  have hya : y+a∈Metric.ball (0 : Plane) R := by
    rw [Metric.mem_ball,dist_zero_right]
    have hh : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hd := ((hg y hy0).contDiffAt (Metric.isOpen_ball.mem_nhds hy0)).differentiableAt (by simp)
  have hda := ((hg (y+a) hya).contDiffAt (Metric.isOpen_ball.mem_nhds hya)).differentiableAt (by simp)
  have hdc : DifferentiableAt ℝ (fun y ↦ g (y+a)) y :=
    hda.comp y (differentiableAt_id.add_const a)
  change fderiv ℝ ((fun y ↦ g (y+a))-g) y v=_
  rw [fderiv_sub hdc hd,fderiv_comp_add_right,
    sub_apply,inner_sub_left,inner_gradient_left,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) :
    ‖gradient g (y+a)-gradient g y‖≤2*(K:ℝ) := by
  have hb (x : Plane) : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])

lemma height_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) : ‖g (y+a)-g y‖≤(K:ℝ)*‖a‖ := by
  simpa only [dist_eq_norm,add_sub_cancel_left] using hg.dist_le_mul (y+a) y

lemma measurable_plane_gradient (g : Plane → ℝ) : Measurable (gradient g) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)

lemma cmc_cutoff_energies_integrable {g η : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (a : Plane) :
    Integrable (fun y ↦ η y^2*‖gradient g (y+a)-gradient g y‖^2) ∧
    Integrable (fun y ↦ (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  obtain ⟨M,hMb⟩ := hη.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hM (y : Plane) : ‖η y‖≤M := hMb (mem_range_self y)
  have hM0 : 0≤M := (norm_nonneg (η 0)).trans (hM 0)
  obtain ⟨D,hD⟩ := hη.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hDη (y : Plane) := norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)
  have hgrad := measurable_plane_gradient g
  have hgrad' : Measurable (fun y ↦ gradient g (y+a)-gradient g y) :=
    (hgrad.comp (measurable_id.add_const a)).sub hgrad
  constructor
  · apply integrable_bounded_compact (hη.continuous.measurable.pow_const 2 |>.mul (hgrad'.norm.pow_const 2)) hc
      (M := M^2*(2*(K:ℝ))^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : η y^2≤M^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hM y) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (gradient_difference_norm_le hg y a) 2)
        (sq_nonneg _) (sq_nonneg M)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]
  · have hm : Measurable (fun y ↦ g (y+a)-g y) :=
      (hg.continuous.measurable.comp (measurable_id.add_const a)).sub hg.continuous.measurable
    apply integrable_bounded_compact ((hm.pow_const 2).mul ((measurable_fderiv ℝ η).norm.pow_const 2)) hc
      (M := ((K:ℝ)*‖a‖)^2*(D:ℝ)^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (hDη y) 2)
        (sq_nonneg _) (sq_nonneg _)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [fderiv_of_notMem_tsupport ℝ hy,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]

theorem WeakCMCGraph.caccioppoli {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hr : 0 < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η⊆Metric.ball 0 r) :
    (∫ y, η y^2*‖gradient g (y+a)-gradient g y‖^2) ≤
      1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  let w : Plane → ℝ := fun y ↦ g (y+a)-g y
  let F : Plane → Plane := fun y ↦ cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)
  let ψ : Plane → ℝ := fun y ↦ η y^2*w y
  have hwc := translated_difference_contDiffOn hgc ha
  have hψ : ContDiff ℝ 1 ψ := local_C1_cutoff_product Metric.isOpen_ball hη hwc hs
  have hψs : tsupport ψ⊆tsupport η := energyTest_tsupport
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset isClosed_closure hψs
  have heq : (∫ y, fderiv ℝ ψ y (F y))=0 := hw.difference_test hg hr ha hψ hψc (hψs.trans hs)
  have hb (y : Plane) : ‖gradient g y‖≤1 := by
    rw [plane_gradient_norm]; exact (norm_fderiv_le_of_lipschitz ℝ hg).trans hK
  have hFm : Measurable F :=
    ((measurable_cmc_gradient g).comp (measurable_id.add_const a)).sub (measurable_cmc_gradient g)
  have hFb (y : Plane) : ‖F y‖≤4 := by
    exact (cmcFlux_difference_bound (hb y) (hb (y+a))).trans
      (by nlinarith [gradient_difference_norm_le hg y a])
  have hFi := integrable_differential_apply_of_bounded hFm hFb hψ hψc
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg hη hc a
  have hpoint (y : Plane) :
      (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
        64*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) ≤ fderiv ℝ ψ y (F y) := by
    by_cases hy : y∈tsupport η
    · have hdη := hη.differentiable (by simp) y
      have hdw := ((hwc y (hs hy)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hy))).differentiableAt (by simp)
      have hd : fderiv ℝ ψ y (F y) =
          η y^2*⟪gradient g (y+a)-gradient g y,F y⟫+2*η y*w y*fderiv ℝ η y (F y) := by
        change fderiv ℝ (fun z ↦ (η^2) z*(g (z+a)-g z)) y (F y)=_
        rw [fderiv_fun_mul (hdη.pow 2) hdw,fderiv_pow 2 hdη]
        change (η y^2 • fderiv ℝ (fun z ↦ g (z+a)-g z) y + (g (y+a)-g y) •
          ((2 • η y^(2-1)) • fderiv ℝ η y)) (F y)=_
        simp only [add_apply,smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,two_smul]
        rw [translated_difference_fderiv hgc ha (hs hy)]
        ring
      rw [hd]
      convert cmc_energy_absorption (hb y) (hb (y+a)) (η y) (w y) (fderiv ℝ η y) using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [w,F]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy,
        fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h)),zero_apply,norm_zero]
      norm_num
  have hInt := integral_mono ((hAi.const_mul (1/16)).sub (hBi.const_mul 64)) hFi hpoint
  simp only [Pi.sub_apply] at hInt
  rw [integral_sub (hAi.const_mul (1/16)) (hBi.const_mul 64),integral_const_mul,
    integral_const_mul,heq] at hInt
  linarith

end CubicTorus

end
end

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

lemma cmcFlux_quadratic_remainder : ∃ L : ℝ, 0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 →
    ‖cmcFlux q-cmcFlux p-cmcJacobian p (q-p)‖≤L*‖q-p‖^2 := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  have hp' : p∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp
  have hq' : q∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hq
  have hs := (convex_closedBall (0 : Plane) (1 : ℝ)).segment_subset hp' hq'
  let F : Plane → Plane := fun x ↦ cmcFlux x-cmcFlux p-cmcJacobian p (x-p)
  have hd (x : Plane) : HasFDerivAt F (cmcJacobian x-cmcJacobian p) x := by
    exact ((cmcFlux_hasFDerivAt x).sub_const (cmcFlux p)).sub
      ((cmcJacobian p).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)) |>.congr_fderiv
        (by simp)
  have hb (x : Plane) (hx : x∈segment ℝ p q) :
      ‖cmcJacobian x-cmcJacobian p‖≤(L:ℝ)*‖q-p‖ := by
    exact (hL.norm_sub_le (hs hx) hp').trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) L.coe_nonneg)
  have hh := (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ ↦ (hd x).hasFDerivWithinAt) hb (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  simpa only [F,sub_self,map_zero,sub_zero,mul_assoc,← pow_two] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_derivative_square_integrable {η : Plane → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun y ↦ ‖fderiv ℝ η y‖^2) := by
  have hd : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by simp)
  have hdc : HasCompactSupport (fderiv ℝ η) := hc.fderiv ℝ
  have hsc : HasCompactSupport (fun y ↦ ‖fderiv ℝ η y‖^2) := by
    apply hdc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    contrapose! hy
    simp only [Function.mem_support,not_not] at hy ⊢
    simp [hy]
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport hsc

theorem WeakCMCGraph.local_gradient_energy {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r s : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hs : 0 < s) (hsr : s < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ C : ℝ, 0≤C ∧ ∀ a : Plane, r+‖a‖≤R →
      (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2)≤C*‖a‖^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨s,(s+r)/2,hs,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hi := compact_derivative_square_integrable (b.contDiff (n := 1)) b.hasCompactSupport
  let C : ℝ := 1024*(K:ℝ)^2*(∫ y, ‖fderiv ℝ b y‖^2)
  have hC : 0≤C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ sq_nonneg _))
  refine ⟨C,hC,fun a ha ↦ ?_⟩
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg (b.contDiff (n := 1)) b.hasCompactSupport a
  have hbound : (∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)≤
      ((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hBi (hi.const_mul _)
    intro y
    have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fderiv ℝ b y‖)]
  calc
    (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2) =
        ∫ y in Metric.ball 0 s, b y^2*‖gradient g (y+a)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
      simp
    _ ≤ ∫ y, b y^2*‖gradient g (y+a)-gradient g y‖^2 :=
      setIntegral_le_integral hAi (ae_of_all _ (fun _ ↦ by positivity))
    _ ≤ 1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2) :=
      hw.caccioppoli hg hK hgc (by linarith) ha b.contDiff b.hasCompactSupport hbs
    _ ≤ 1024*(((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2)) := by linarith
    _ = C*‖a‖^2 := by dsimp only [C]; ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace CubicTorus
universe uHilbert

theorem hilbert_bounded_weak_subsequence {E : Type uHilbert}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (f : ℕ → E) {M : ℝ}
    (hb : ∀ i, ‖f i‖≤M) :
    ∃ (u : E) (φ : ℕ → ℕ), ‖u‖≤M ∧ StrictMono φ ∧
      ∀ v : E, Tendsto (fun i ↦ ⟪f (φ i),v⟫) atTop (𝓝 ⟪u,v⟫) := by
  let F : ℕ → WeakDual ℝ E := fun i ↦ StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (f i))
  have hm (i : ℕ) : F i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ E) (f i)‖≤M
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hb i
  obtain ⟨L,hL,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hm
  let u : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L)
  refine ⟨u,φ,?_,hφ,fun v ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm _‖≤M
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hL
  · have hh := ((WeakDual.eval_continuous v).tendsto L).comp hlim
    simpa only [F,Function.comp_def,StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply,
      u,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_difference_quotient_pairing {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (v : Plane) :
    (∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y)=
      ∫ y, (t⁻¹*(ψ (y+t • (-v))-ψ y))*f y := by
  have h₁ : Integrable (fun y ↦ f (y+t • v)*ψ y) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₂ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₃ : Integrable (fun y ↦ f y*ψ (y+t • (-v))) :=
    (hf.mul (hψ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  have he : (∫ y, f (y+t • v)*ψ y)=(∫ y, f y*ψ (y+t • (-v))) := by
    rw [← integral_add_right_eq_self _ (t • (-v))]
    simp
  simp_rw [mul_assoc,← mul_comm (f _),sub_mul,mul_sub]
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _),
    integral_sub (h₃.const_mul _) (h₂.const_mul _),integral_const_mul,integral_const_mul,
    integral_const_mul,he]

theorem continuous_difference_quotient_test_limit {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (v : Plane) :
    Tendsto (fun t : ℝ ↦ ∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y) (𝓝[>] 0)
      (𝓝 (-(∫ y, f y*fderiv ℝ ψ y v))) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hh := LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (μ := (volume : Measure Plane)) hL hc hf (-v)
  have he : (∫ y, lineDeriv ℝ ψ y (-v)*f y)= -(∫ y, f y*fderiv ℝ ψ y v) := by
    simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
      map_neg,neg_mul,integral_neg,mul_comm _ (f _)]
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact continuous_difference_quotient_pairing hf hψ.continuous hc t v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_continuousOn {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiffOn ℝ 1 g U) (hU : IsOpen U) : ContinuousOn (gradient g) U :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma differenceStep_mem {δ : ℝ} (hδ : 0<δ) (i : ℕ) : differenceStep δ i∈Ioc 0 δ := by
  have hn : (1:ℝ)≤(i:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · dsimp only [differenceStep]; positivity
  · dsimp only [differenceStep]
    exact mul_le_of_le_one_right hδ.le (by rw [div_le_one (by linarith : (0:ℝ)<(i:ℝ)+1)]; exact hn)

lemma differenceStep_tendsto {δ : ℝ} (hδ : 0<δ) : Tendsto (differenceStep δ) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall (fun i ↦ (differenceStep_mem hδ i).1)⟩
  change Tendsto (fun i : ℕ ↦ δ*(1/((i:ℝ)+1))) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

lemma L2_vector_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp Plane 2 μ) : ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem vector_L2_difference_subsequence {f : Plane → Plane}
    (hf : Continuous f) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    {r δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (v : Plane)
    (he : ∀ t∈Ioc 0 δ, (∫ y in Metric.ball 0 r, ‖f (y+t • v)-f y‖^2)≤C*t^2) :
    ∃ (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))) (φ : ℕ → ℕ),
      ‖u‖≤Real.sqrt C ∧ StrictMono φ ∧
      ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
        Tendsto (fun i ↦ ⟪(vectorDifference_memLp hf hb r (differenceStep δ (φ i)) v).toLp
          (vectorDifference f v (differenceStep δ (φ i))),V⟫) atTop (𝓝 ⟪u,V⟫) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  let Q : ℕ → Lp Plane 2 μ := fun i ↦ (vectorDifference_memLp hf hb r (differenceStep δ i) v).toLp
    (vectorDifference f v (differenceStep δ i))
  have hQ (i : ℕ) : ‖Q i‖≤Real.sqrt C := by
    have heq : ‖Q i‖^2=(differenceStep δ i)⁻¹^2*
        (∫ y in Metric.ball 0 r, ‖f (y+differenceStep δ i • v)-f y‖^2) := by
      rw [L2_vector_norm_sq_integral]
      calc
        _ = ∫ y, ‖vectorDifference f v (differenceStep δ i) y‖^2 ∂μ := integral_congr_ae
          ((vectorDifference_memLp hf hb r (differenceStep δ i) v).coeFn_toLp.mono (fun y hy ↦ by rw [hy]))
        _ = _ := by simp only [vectorDifference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul,μ]
    have hh := mul_le_mul_of_nonneg_left (he _ (differenceStep_mem hδ i)) (sq_nonneg (differenceStep δ i)⁻¹)
    have htne := (differenceStep_mem hδ i).1.ne'
    have hsq := Real.sq_sqrt hC
    have hre : (differenceStep δ i)⁻¹^2*(C*(differenceStep δ i)^2)=C := by field_simp
    rw [hre,← heq] at hh
    nlinarith [norm_nonneg (Q i),Real.sqrt_nonneg C]
  exact hilbert_bounded_weak_subsequence Q hQ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_vector_cutoff {f : Plane → Plane} {η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y • f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.smul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:Plane))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

theorem WeakCMCGraph.gradient_difference_data {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (G : Plane → Plane) (C : ℝ), Continuous G ∧ (∀ y, ‖G y‖≤1) ∧ 0≤C ∧
      (∀ y, ‖y‖≤R/2 → G y=gradient g y) ∧
      ∀ v : Plane, ‖v‖≤1 → ∀ t∈Ioc 0 (R/4),
        (∫ y in Metric.ball 0 (R/4), ‖G (y+t • v)-G y‖^2)≤C*t^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let G : Plane → Plane := fun y ↦ b y • gradient g y
  have hGc : Continuous G := continuous_local_vector_cutoff Metric.isOpen_ball
    (C1_gradient_continuousOn hgc Metric.isOpen_ball) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hGb (y : Plane) : ‖G y‖≤1 := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact ((mul_le_mul_of_nonneg_left (hgrad y) b.nonneg).trans
      (mul_le_of_le_one_left K.coe_nonneg b.le_one)).trans hK
  have hGeq {y : Plane} (hy : ‖y‖≤R/2) : G y=gradient g y := by
    dsimp only [G]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_smul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hK hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  refine ⟨G,C,hGc,hGb,hC,fun _ hy ↦ hGeq hy,fun v hv t ht ↦ ?_⟩
  have ha : ‖t • v‖≤t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact mul_le_of_le_one_right ht.1.le hv
  calc
    _ = ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      dsimp only
      rw [hGeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hGeq (by linarith)]
    _ ≤ C*‖t • v‖^2 := henergy (t • v) (by linarith [ht.2])
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem vector_weak_quotient_derivative {f : Plane → Plane} (hf : Continuous f)
    {r : ℝ} {t : ℕ → ℝ} (htlim : Tendsto t atTop (𝓝[>] 0)) (v w : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y)= -(∫ y, ⟪f y,w⟫*fderiv ℝ ψ y v) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let W : Plane → Plane := fun y ↦ ψ y • w
  have hWc : Continuous W := hψ.continuous.smul continuous_const
  have hWs : HasCompactSupport W := hc.smul_right
  have hWm : MemLp W 2 μ := hWc.memLp_of_hasCompactSupport hWs
  let V : Lp Plane 2 μ := hWm.toLp W
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, ((t i)⁻¹*(⟪f (y+t i • v),w⟫-⟪f y,w⟫))*ψ y) := by
    rw [L2.inner_def,integral_mul_eq_restrict_of_tsupport measurableSet_ball _ ψ hs]
    apply integral_congr_ae
    filter_upwards [hQ i,hWm.coeFn_toLp] with y hy hy'
    rw [hy,hy']
    simp only [W,vectorDifference,inner_smul_right,inner_smul_left,inner_sub_left,RCLike.conj_to_real]
    ring
  have hup : ⟪u,V⟫=(∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWm.coeFn_toLp] with y hy
    rw [hy]
    simp only [W,inner_smul_right]
    ring
  have hlim₁ := hw V
  simp_rw [hp,hup] at hlim₁
  have hlim₂ := (continuous_difference_quotient_test_limit (hf.inner (continuous_const (y := w))) hψ hc v).comp htlim
  exact tendsto_nhds_unique hlim₁ hlim₂

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weak_L2_cmc_chain {f : Plane → Plane} (hf : Continuous f)
    (hb : ∀ y, ‖f y‖≤1) {r C : ℝ} (hC : 0≤C) {t : ℕ → ℝ}
    (ht : ∀ i, 0<t i) (htlim : Tendsto t atTop (𝓝 0))
    (v : Plane)
    (henergy : ∀ i, (∫ y in Metric.ball 0 r, ‖f (y+t i • v)-f y‖^2)≤C*(t i)^2)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,
      fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)))) atTop
      (𝓝 (∫ y in Metric.ball 0 r, fderiv ℝ ψ y (cmcJacobian (f y) (u y)))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨B,hB,hrem⟩ := cmcFlux_quadratic_remainder
  have hgrad (y : Plane) : ‖gradient ψ y‖≤(L:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
  let W : Plane → Plane := fun y ↦ cmcJacobian (f y) (gradient ψ y)
  have hWcont : Continuous W := (cmcJacobian_contDiff.continuous.comp hf).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) :=
    (cmcJacobian_norm_le (hb y) _).trans (by gcongr; exact hgrad y)
  have hW : MemLp W 2 μ := MemLp.of_bound hWcont.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  let V : Lp Plane 2 μ := hW.toLp W
  have hid (y z : Plane) : ⟪z,W y⟫=fderiv ℝ ψ y (cmcJacobian (f y) z) := by
    dsimp only [W]
    rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  have hup : ⟪u,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (u y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with y hy
    rw [hy,hid]
  have hlim := hw V
  rw [hup] at hlim
  simp_rw [hp] at hlim
  let Err : ℕ → Plane → ℝ := fun i y ↦ fderiv ℝ ψ y ((t i)⁻¹ •
    (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)))
  have herr (i : ℕ) : ‖∫ y, Err i y ∂μ‖≤((L:ℝ)*B*C)*t i := by
    have hti : 0<(t i)⁻¹ := inv_pos.mpr (ht i)
    have hei : Integrable (fun y ↦ ‖f (y+t i • v)-f y‖^2) μ := by
      apply (integrable_const (4:ℝ)).mono' (by fun_prop)
      filter_upwards [] with y
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
      nlinarith [norm_nonneg (f (y+t i • v)-f y)]
    calc
      _ ≤ ∫ y, ((L:ℝ)*B*(t i)⁻¹)*‖f (y+t i • v)-f y‖^2 ∂μ := by
        apply norm_integral_le_of_norm_le (hei.const_mul _)
        filter_upwards [] with y
        dsimp only [Err]
        calc
          _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
              (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
          _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
            rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
          _ ≤ (L:ℝ)*((t i)⁻¹*(B*‖f (y+t i • v)-f y‖^2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (hrem _ _ (hb y) (hb (y+t i • v))) hti.le) L.coe_nonneg
          _ = _ := by ring
      _ = ((L:ℝ)*B*(t i)⁻¹)*(∫ y, ‖f (y+t i • v)-f y‖^2 ∂μ) := integral_const_mul _ _
      _ ≤ ((L:ℝ)*B*(t i)⁻¹)*(C*(t i)^2) := by
        simpa only [mul_comm] using mul_le_mul (henergy i)
          (le_refl ((L:ℝ)*B*(t i)⁻¹)) (by positivity) (mul_nonneg hC (sq_nonneg (t i)))
      _ = _ := by field_simp
  have herrlim : Tendsto (fun i ↦ ∫ y, Err i y ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm herr (by simpa using htlim.const_mul ((L:ℝ)*B*C))
  have hsum := hlim.add herrlim
  simp only [add_zero] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  have hEi : Integrable (Err i) μ := by
    apply (integrable_const ((L:ℝ)*(t i)⁻¹*8)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      dsimp only [Err]
      have hD := hψ.continuous_fderiv (by simp)
      have hF := cmcFlux_contDiff.continuous
      have hJ := cmcJacobian_contDiff.continuous
      fun_prop
    · filter_upwards [] with y
      dsimp only [Err]
      have hrem8 : ‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖≤8 := by
        have hd : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
        have h₁ := cmcFlux_difference_bound (hb y) (hb (y+t i • v))
        have h₂ := cmcJacobian_norm_le (hb y) (f (y+t i • v)-f y)
        exact (norm_sub_le _ _).trans (by linarith)
      calc
        _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
        _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
        _ ≤ (L:ℝ)*((t i)⁻¹*8) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrem8 (inv_pos.mpr (ht i)).le) L.coe_nonneg
        _ = _ := by ring
  have hJi : Integrable (fun y ↦ fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y))) μ := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (Q i) V
    apply hi.congr
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  rw [← integral_add hJi hEi]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp only [Err,vectorDifference]
  simp only [map_sub,map_smul,smul_eq_mul]
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

lemma differential_integral_restrict {ψ : Plane → ℝ} {S : Set Plane}
    (hs : tsupport ψ⊆S) (F : Plane → Plane) :
    (∫ y in S, fderiv ℝ ψ y (F y))=(∫ y, fderiv ℝ ψ y (F y)) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy')),zero_apply]

theorem WeakCMCGraph.linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      (∀ (w : Plane) (ψ : Plane → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), ⟪u y,w⟫*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)) ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (gradient g y) (u y)))=0) := by
  obtain ⟨G,C,hGc,hGb,hC,hGeq,henergy⟩ := hcmc.gradient_difference_data hg hK hR hgc
  have hδ : 0<R/4 := by linarith
  obtain ⟨u,φ,_hu,hφ,hw⟩ := vector_L2_difference_subsequence hGc hGb hδ hC v (henergy v hv)
  let t : ℕ → ℝ := fun i ↦ differenceStep (R/4) (φ i)
  let Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))) := fun i ↦
    (vectorDifference_memLp hGc hGb (R/4) (t i) v).toLp (vectorDifference G v (t i))
  have ht (i : ℕ) : t i∈Ioc 0 (R/4) := differenceStep_mem hδ (φ i)
  have htlim : Tendsto t atTop (𝓝[>] 0) := (differenceStep_tendsto hδ).comp hφ.tendsto_atTop
  have hQ (i : ℕ) : (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) (R/4))]
      vectorDifference G v (t i) := (vectorDifference_memLp hGc hGb (R/4) (t i) v).coeFn_toLp
  have hweak : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫) := hw
  have hty (i : ℕ) : ‖t i • v‖≤t i := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ht i).1]
    exact mul_le_of_le_one_right (ht i).1.le hv
  have hGy (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hGyt (i : ℕ) (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) :
      G (y+t i • v)=gradient g (y+t i • v) := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (by linarith [hty i,(ht i).2])
  refine ⟨u,?_,?_⟩
  · intro w ψ hψ hc hs
    rw [vector_weak_quotient_derivative hGc htlim v w hQ hweak hψ hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈tsupport ψ
    · rw [hGy y (hs hy)]
    · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    have hlim := weak_L2_cmc_chain hGc hGb hC (fun i ↦ (ht i).1)
      (tendsto_nhds_of_tendsto_nhdsWithin htlim) v (fun i ↦ henergy v hv (t i) (ht i)) hQ hweak hψ hc
    have hzero (i : ℕ) : (∫ y in Metric.ball 0 (R/4),
        fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (G (y+t i • v))-cmcFlux (G y))))=0 := by
      calc
        _ = ∫ y in Metric.ball 0 (R/4),
            fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          dsimp only
          rw [hGy y hy,hGyt i y hy]
        _ = ∫ y, fderiv ℝ ψ y ((t i)⁻¹ •
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := differential_integral_restrict hs _
        _ = (t i)⁻¹*(∫ y, fderiv ℝ ψ y
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          simp only [map_smul,smul_eq_mul,integral_const_mul]
        _ = 0 := by
          rw [hcmc.difference_test hg hδ (by linarith [hty i,(ht i).2]) hψ hc hs,mul_zero]
    have he : (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (G y) (u y)))=0 :=
      tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [hGy y hy]

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

lemma C1_mixed_test_identity {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S)
    (v w : Plane) :
    (∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)=
      (∫ y, ⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y w) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  simp only [inner_gradient_left]
  rw [C1_local_integration_by_parts hS hg hgc (hv.of_le (by simp))
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset (f := ψ) ℝ v).trans hs) w,
    C1_local_integration_by_parts hS hg hgc (hw.of_le (by simp))
    (hc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset (f := ψ) ℝ w).trans hs) v]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [fderiv_fderiv_apply hψ,fderiv_fderiv_apply hψ]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma indicator_inner_test_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (v : Plane) (ψ : Plane → ℝ) :
    (∫ y,⟪S.indicator U y,v⟫*ψ y)=(∫ y in S,⟪U y,v⟫*ψ y) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

lemma indicator_differential_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (A : Plane → Plane →L[ℝ] Plane) (ψ : Plane → ℝ) :
    (∫ y,fderiv ℝ ψ y (A y (S.indicator U y)))=
      (∫ y in S,fderiv ℝ ψ y (A y (U y))) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

theorem WeakCMCGraph.scalar_linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ (u : Lp ℝ 2 (volume : Measure Plane)) (U : Lp Plane 2 (volume : Measure Plane)),
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/4))]
        (fun y ↦ fderiv ℝ g y v) ∧
      PlaneWeakGradient (Metric.ball 0 (R/4)) u U ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (U y)))=0) := by
  let S : Set Plane := Metric.ball 0 (R/4)
  obtain ⟨F,hF,hlin⟩ := hcmc.linearized_equation hg hK hR hgc v hv
  have hFmem : MemLp (S.indicator (F : Plane → Plane)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp F)
  let U := hFmem.toLp (S.indicator (F : Plane → Plane))
  let b : ContDiffBump (0 : Plane) := ⟨R/4,R/2,by linarith,by linarith⟩
  let f : Plane → ℝ := fun y ↦ fderiv ℝ g y v*b y
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hfc : Continuous f := continuous_local_scalar_product Metric.isOpen_ball
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const)
    b.continuous hbs
  have hfs : HasCompactSupport f := b.hasCompactSupport.mul_left
  have hfmem : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  let u := hfmem.toLp f
  have hfe (y : Plane) (hy : y∈S) : f y=fderiv ℝ g y v := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),mul_one]
  refine ⟨u,U,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hfmem.coeFn_toLp,ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hs
    exact hy.trans (hfe y hs)
  · intro w ψ hψ hc hs
    have hψs : tsupport ψ⊆Metric.ball 0 R := hs.trans (Metric.ball_subset_ball (by linarith))
    calc
      _ = ∫ y,⟪S.indicator (F : Plane → Plane) y,w⟫*ψ y := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,⟪F y,w⟫*ψ y := indicator_inner_test_integral measurableSet_ball _ _ _
      _ = -(∫ y,⟪gradient g y,w⟫*fderiv ℝ ψ y v) := hF w ψ (hψ.of_le (by simp)) hc hs
      _ = -(∫ y,⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
        rw [C1_mixed_test_identity Metric.isOpen_ball hg.continuous hgc hψ hc hψs v w]
      _ = -(∫ y,u y*fderiv ℝ ψ y w) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfmem.coeFn_toLp] with y hy
        rw [hy,inner_gradient_left]
        by_cases hyS : y∈S
        · rw [hfe y hyS]
        · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hyS (hs h)),zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    calc
      _ = ∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (S.indicator (F : Plane → Plane) y)) := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (gradient g y) (F y)) :=
        indicator_differential_integral measurableSet_ball _ _ _
      _ = 0 := hlin ψ (hψ.of_le (by simp)) hc hs

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

lemma cmcJacobian_uniform_lipschitz : ∃ L : ℝ,0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 → ‖cmcJacobian p-cmcJacobian q‖≤L*‖p-q‖ := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  exact hL.norm_sub_le (by simpa using hp) (by simpa using hq)

end CubicTorus

end
end

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

lemma cmcStretch_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcStretch p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p+1 := by linarith
  have hi : (cmcWeight p+1)⁻¹≤1 := (inv_le_one₀ h0).mpr (by linarith)
  rw [cmcStretch_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p+1)⁻¹*⟪p,v⟫) • p‖ := norm_add_le _ _
    _ = ‖v‖+(cmcWeight p+1)⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

lemma cmcCompress_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcCompress p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p*(cmcWeight p+1) := by positivity
  have hi : (cmcWeight p*(cmcWeight p+1))⁻¹≤1 := (inv_le_one₀ h0).mpr (by nlinarith)
  rw [cmcCompress_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = ‖v‖+(cmcWeight p*(cmcWeight p+1))⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma PlaneWeakGradient.unique {S : Set Plane} (hS : IsOpen S)
    {u : Plane → ℝ} {G H : Plane → Plane}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (huG : PlaneWeakGradient S u G) (huH : PlaneWeakGradient S u H) :
    G=ᵐ[volume.restrict S] H := by
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hG.sub hH).locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · change ∀ᵐ y ∂volume.restrict S, G y = H y
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [hz] with y hy hys
    exact sub_eq_zero.mp (hy hys)
  · have hiG := hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have hiH := hH.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    simp only [Pi.sub_apply,smul_sub,integral_sub hiG hiH]
    apply sub_eq_zero.mpr
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hiG v,← integral_inner hiH v]
    simp only [inner_smul_right]
    simp_rw [real_inner_comm (G _) v,real_inner_comm (H _) v]
    simpa only [mul_comm] using (huG v ψ hψ hc hs).trans (huH v ψ hψ hc hs).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

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
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

lemma LinearCMCEquation.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane} {U : Set Plane}
    (hU : IsOpen U) (hw : LinearCMCEquation g p B U)
    (hg : EqOn g' g U) (hp : EqOn p' p U) (hB : EqOn B' B U) : LinearCMCEquation g' p' B' U := by
  intro ψ hψ hc hs
  rw [← hw ψ hψ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    by_cases hy : y∈U
    · have he : g'=ᶠ[𝓝 y]g := by
        filter_upwards [hU.mem_nhds hy] with z hz
        exact hg hz
      have hG : gradient g' y=gradient g y := congrArg
        (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) he.fderiv_eq
      rw [hG,hp hy,hB hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.continuousAt [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ContinuousAt f x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hd : Tendsto (fun y : E ↦ dist y x) (𝓝 x) (𝓝 0) := by
    simpa only [id_eq,dist_self] using ((continuous_id : Continuous (fun y : E ↦ y)).dist (continuous_const (y := x))).tendsto x
  have hlim : Tendsto (fun y : E ↦ C*(dist y x)^α) (𝓝 x) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne',mul_zero] using (hd.rpow_const (Or.inr hα.le)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact hH y hy x (Metric.mem_ball_self hr)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.eventually [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ∀ᶠ y in 𝓝 x,HolderNear f y := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < r/2)] with y hy
  have hsub : Metric.ball y (r/2)⊆Metric.ball x r := by
    intro z hz
    have hz' := Metric.mem_ball.mp hz
    have hy' := Metric.mem_ball.mp hy
    have ht := dist_triangle z y x
    exact Metric.mem_ball.mpr (by linarith)
  exact ⟨r/2,α,C,by linarith,hα,hα1,hC,fun z hz w hw ↦ hH z (hsub hz) w (hsub hw)⟩

lemma HolderNear.contDiffAt_zero {f : E → F} {x : E} (hf : HolderNear f x) : ContDiffAt ℝ 0 f x := by
  obtain ⟨s,hS,hsc,hs⟩ := eventually_nhds_iff.mp hf.eventually
  exact _root_.contDiffAt_zero.mpr ⟨s,hsc.mem_nhds hs,fun y hy ↦ (hS y hy).continuousAt.continuousWithinAt⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.congr [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : HolderNear f x) (he : f=ᶠ[𝓝 x]g) : HolderNear g x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsE⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,α,C,lt_min hr hs,hα,hα1,hC,?_⟩
  intro y hy z hz
  have hyR := (Metric.ball_subset_ball (min_le_left r s)) hy
  have hzR := (Metric.ball_subset_ball (min_le_left r s)) hz
  rw [← hsE ((Metric.ball_subset_ball (min_le_right r s)) hy),
    ← hsE ((Metric.ball_subset_ball (min_le_right r s)) hz)]
  exact hH y hyR z hzR

lemma ContDiffAt.holderNear {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) : HolderNear f x := by
  obtain ⟨C,S,hS,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r,1,C,hr,by norm_num,le_rfl,C.coe_nonneg,?_⟩
  intro y hy z hz
  simpa only [Real.rpow_one] using hLip.dist_le_mul y (hrS hy) z (hrS hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
lemma HolderNear.prodMk [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) : HolderNear (fun y ↦ (f y,g y)) x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,β,D,hs,hβ,hβ1,hD,hJ⟩ := hg
  let ρ := min (min r s) (1/2)
  have hρ : 0<ρ := lt_min (lt_min hr hs) (by norm_num)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hρα : ρ≤1/2 := min_le_right _ _
  refine ⟨ρ,min α β,C+D,hρ,lt_min hα hβ,(min_le_left _ _).trans hα1,add_nonneg hC hD,?_⟩
  intro y hy z hz
  have hd : dist y z≤1 := by
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have ht := dist_triangle_right y z x
    linarith
  have hhα : (dist y z)^α≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_left _ _)
  have hhβ : (dist y z)^β≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_right _ _)
  rw [Prod.dist_eq]
  apply max_le
  · exact ((hH y ((Metric.ball_subset_ball hρr) hy) z ((Metric.ball_subset_ball hρr) hz)).trans
      (mul_le_mul_of_nonneg_left hhα hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
  · exact ((hJ y ((Metric.ball_subset_ball hρs) hy) z ((Metric.ball_subset_ball hρs) hz)).trans
      (mul_le_mul_of_nonneg_left hhβ hD)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))

lemma ContDiffAt.comp_holderNear {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ 1 g (f x)) (hf : HolderNear f x) : HolderNear (g ∘ f) x := by
  obtain ⟨K,S,hS,hLip⟩ := hg.exists_lipschitzOnWith
  have hfcont := hf.continuousAt
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsS⟩ := Metric.mem_nhds_iff.mp (hfcont hS)
  refine ⟨min r s,α,(K:ℝ)*C,lt_min hr hs,hα,hα1,mul_nonneg K.coe_nonneg hC,?_⟩
  intro y hy z hz
  calc
    _ ≤ (K:ℝ)*dist (f y) (f z) := hLip.dist_le_mul (f y)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hy)) (f z)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hz))
    _ ≤ (K:ℝ)*(C*(dist y z)^α) := mul_le_mul_of_nonneg_left
      (hH y ((Metric.ball_subset_ball (min_le_left r s)) hy)
        z ((Metric.ball_subset_ball (min_le_left r s)) hz)) K.coe_nonneg
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.congr {n : ℕ} {f g : E → F} {x : E} (hf : HolderJet n f x)
    (he : f=ᶠ[𝓝 x]g) : HolderJet n g x := by
  induction n generalizing F with
  | zero => exact hf.congr he
  | succ n ih =>
    exact ⟨hf.1.congr_of_eventuallyEq he.symm,ih hf.2 he.fderiv⟩

lemma HolderJet.pred {n : ℕ} {f : E → F} {x : E} (hf : HolderJet (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf.1
  | succ n ih => exact ⟨hf.1,ih hf.2⟩

lemma HolderJet.contDiffAt {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : ContDiffAt ℝ n f x := by
  induction n generalizing F with
  | zero => exact HolderNear.contDiffAt_zero hf
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fderiv ℝ f,?_,ih hf.2⟩
    have hdiff : ∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y :=
      (hf.1.eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one
    exact ⟨{y|DifferentiableAt ℝ f y},hdiff,fun y hy ↦ hy.hasFDerivAt⟩

lemma ContDiffAt.holderJet {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf
  | succ n ih =>
    refine ⟨hf.of_le (by norm_cast; omega),?_⟩
    exact ih (hf.fderiv_right (by norm_cast))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.eventually {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) :
    ∀ᶠ y in 𝓝 x,HolderJet n f y := by
  induction n generalizing F with
  | zero => exact HolderNear.eventually hf
  | succ n ih => exact (hf.1.eventually (by simp)).and (ih hf.2)

lemma HolderJet.clm_comp {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x)
    (L : F →L[ℝ] G) : HolderJet n (L ∘ f) x := by
  induction n generalizing F G with
  | zero => exact ContDiffAt.comp_holderNear L.contDiff.contDiffAt hf
  | succ n ih =>
    refine ⟨L.contDiff.contDiffAt.comp x hf.1,?_⟩
    apply (ih hf.2 (ContinuousLinearMap.compL ℝ E F G L)).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact ((L.hasFDerivAt).comp y hy.differentiableAt_one.hasFDerivAt).fderiv.symm

lemma HolderJet.prodMk {n : ℕ} {f : E → F} {g : E → G} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ (f y,g y)) x := by
  induction n generalizing F G with
  | zero => exact HolderNear.prodMk hf hg
  | succ n ih =>
    refine ⟨hf.1.prodMk hg.1,?_⟩
    have hh := (ih hf.2 hg.2).clm_comp
      (ContinuousLinearMap.prodₗᵢ ℝ (E := E) (F := F) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap
    apply hh.congr
    filter_upwards [hf.1.eventually (by simp),hg.1.eventually (by simp)] with y hy hz
    exact (hy.differentiableAt_one.fderiv_prodMk hz.differentiableAt_one).symm

lemma HolderJet.smooth_comp {n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : HolderJet n f x) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : HolderJet n (g ∘ f) x := by
  induction n generalizing E F G with
  | zero => exact ContDiffAt.comp_holderNear (hg.of_le (by simp)).contDiffAt hf
  | succ n ih =>
    refine ⟨(hg.of_le (by simp)).contDiffAt.comp x hf.1,?_⟩
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hpair := (ih hf.pred hDg).prodMk hf.2
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (F →L[ℝ] G)×(E →L[ℝ] F) ↦ p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
    apply (ih hpair hcomp).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact (fderiv_comp y (hg.differentiable (by simp) (f y)) hy.differentiableAt_one).symm

lemma HolderJet.const {n : ℕ} {x : E} (c : F) : HolderJet n (fun _ : E ↦ c) x :=
  ContDiffAt.holderJet contDiffAt_const

lemma HolderJet.clm_apply {n : ℕ} {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y (g y)) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.clm_apply contDiff_snd)

end CubicTorus

end
end

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

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HolderJet.directional {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) (v : Plane) : HolderJet n (fun y ↦ fderiv ℝ f y v) x :=
  hf.2.clm_apply (HolderJet.const v)

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

lemma contDiff_local_vector_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {η : Plane → ℝ} {S : Set Plane} {n : WithTop ℕ∞}
    (hS : IsOpen S) (hf : ContDiffOn ℝ n f S) (hη : ContDiff ℝ n η)
    (hs : tsupport η⊆S) : ContDiff ℝ n (fun y ↦ η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.contDiffAt.smul ((hf y (hs hy)).contDiffAt (hS.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_C1_lipschitz {f : E → F} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0,LipschitzWith K f := by
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨Real.toNNReal C,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x ↦ ?_⟩
  apply NNReal.coe_le_coe.mp
  exact (hC x).trans (Real.le_coe_toNNReal C)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus

lemma HolderJet.extension {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Plane → F} (hf : HolderJet (n+1) f 0) :
    ∃ (f' : Plane → F) (K : ℝ≥0) (M : ℝ),
      ContDiff ℝ (n+1) f' ∧ HasCompactSupport f' ∧ LipschitzWith K f' ∧
      (∀ y,‖f' y‖≤M) ∧ (∀ y,‖f' y‖≤‖f y‖) ∧
      f'=ᶠ[𝓝 0]f ∧ HolderJet (n+1) f' 0 := by
  obtain ⟨r,hr,hjets⟩ := Metric.mem_nhds_iff.mp hf.eventually
  have hfc : ContDiffOn ℝ (n+1) f (Metric.ball 0 r) := fun y hy ↦
    (hjets hy).contDiffAt.contDiffWithinAt
  let b : ContDiffBump (0 : Plane) := ⟨r/2,3*r/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → F := fun y ↦ b y • f y
  have hc : ContDiff ℝ (n+1) f' := contDiff_local_vector_cutoff Metric.isOpen_ball hfc b.contDiff hbs
  have hcs : HasCompactSupport f' := b.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hc.of_le (by norm_cast; omega)) hcs
  obtain ⟨M,hM⟩ := hcs.exists_bound_of_continuous hc.continuous
  have he : f'=ᶠ[𝓝 0]f := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by linarith : 0 < r/2)] with y hy
    dsimp only [f']
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  refine ⟨f',K,M,hc,hcs,hK,hM,?_,he,hf.congr he.symm⟩
  intro y
  dsimp only [f']
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) b.le_one

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquationNear.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane}
    (hw : LinearCMCEquationNear g p B)
    (hg : g'=ᶠ[𝓝 0]g) (hp : p'=ᶠ[𝓝 0]p) (hB : B'=ᶠ[𝓝 0]B) : LinearCMCEquationNear g' p' B' := by
  obtain ⟨R,hR,hw⟩ := hw
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (hg.and (hp.and hB))
  refine ⟨min r R,lt_min hr hR,?_⟩
  have hsub : Metric.ball (0 : Plane) (min r R)⊆Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  exact (hw.mono (Metric.ball_subset_ball (min_le_right _ _))).congr Metric.isOpen_ball
    (fun _ hy ↦ (he (hsub hy)).1) (fun _ hy ↦ (he (hsub hy)).2.1) (fun _ hy ↦ (he (hsub hy)).2.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.directional_linear_near {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hgJ : HolderJet 2 g 0)
    (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquationNear (fun y ↦ fderiv ℝ g y v) (gradient g) (fun _ ↦ 0) := by
  obtain ⟨d,Kd,Md,hdc,_,_,_,_,hde,_⟩ := (hgJ.directional v).extension
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp hde
  obtain ⟨u,G,hue,hug,hlin⟩ := hw.scalar_linearized_equation hg hK hR hgc v hv
  let s := min r (R/4)
  have hs : 0 < s := lt_min hr (by linarith)
  have hsr : s ≤ r := min_le_left _ _
  have hsR : s≤R/4 := min_le_right _ _
  have hsub : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball hsR
  have hdu : PlaneWeakGradient (Metric.ball 0 s) d G := by
    apply (hug.mono hsub).local_congr measurableSet_ball ?_ EventuallyEq.rfl
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hue,
      ae_restrict_mem measurableSet_ball] with y hy hyS
    exact (he ((Metric.ball_subset_ball hsr) hyS)).trans hy.symm
  have hgradc : Continuous (gradient d) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hdc.continuous_fderiv (by simp))
  have hGe := PlaneWeakGradient.unique Metric.isOpen_ball
    ((Lp.memLp G).locallyIntegrable (by norm_num)) hgradc.locallyIntegrable hdu (C1_weak_gradient hdc _)
  have hw' : LinearCMCEquationNear d (gradient g) (fun _ ↦ 0) := by
    refine ⟨s,hs,?_⟩
    intro ψ hψ hc hψs
    simp only [sub_zero]
    rw [← hlin ψ hψ hc (hψs.trans hsub)]
    apply integral_congr_ae
    have het := (ae_restrict_iff' measurableSet_ball).mp hGe
    filter_upwards [het] with y hy
    by_cases hys : y∈Metric.ball (0 : Plane) s
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hys (hψs h))]; rfl
  exact hw'.congr hde.symm EventuallyEq.rfl EventuallyEq.rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_continuous {F : Plane → Plane} (hF : ContDiff ℝ 1 F) :
    Continuous (planeDivergence F) := by
  have hd := hF.continuous_fderiv (by simp)
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const))

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

lemma classical_divergence_of_weak {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {S : Set Plane} (hS : IsOpen S) {H : ℝ}
    (hw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆S →
      (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y)) :
    ∀ y∈S,planeDivergence F y= -H := by
  have hd := (planeDivergence_continuous hF).add (continuous_const (y := H))
  have hae := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrable.locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · have hae' : (fun y ↦ planeDivergence F y+H)=ᵐ[volume.restrict S] (fun _ ↦ (0:ℝ)) := by
      change ∀ᵐ y ∂volume.restrict S,planeDivergence F y+H=0
      rw [ae_restrict_iff' hS.measurableSet]
      exact hae
    have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hd.continuousOn continuousOn_const
    intro y hy
    exact eq_neg_of_add_eq_zero_left (he hy)
  · have hi : Integrable (fun y ↦ planeDivergence F y*ψ y) volume := ((planeDivergence_continuous hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable (fun y ↦ H*ψ y) volume := (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul H
    simp only [smul_eq_mul,Pi.add_apply,mul_add]
    simp_rw [mul_comm (ψ _) (planeDivergence F _),mul_comm (ψ _) H]
    rw [integral_add hi hj,plane_divergence_integration_by_parts hF (hψ.of_le (by simp)) hc,
      hw ψ hψ hc hs,integral_const_mul]
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

theorem graphJacobiForm_transform {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q φ ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    graphJacobiForm A q φ ψ=
      ∫ y,⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgφ := plane_gradient_contDiff hφ
  have hgψ := plane_gradient_contDiff hψ
  let F : Plane → Plane := fun y ↦ A y (gradient q y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hA.clm_apply hgq
  have htest : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ q y*φ y*ψ y) := (hq.mul hφ).mul hψ
  have htestc : HasCompactSupport (fun y ↦ q y*φ y*ψ y) := hc.mul_left
  have hibp := plane_divergence_integration_by_parts (hF.of_le (by simp))
    (htest.of_le (by simp)) htestc
  have hmain : Integrable (fun y ↦ (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫) := by
    apply ((hq.continuous.pow 2).mul (hgφ.continuous.inner (hA.continuous.clm_apply hgψ.continuous))).integrable_of_hasCompactSupport
    apply hc.mono'
    intro y hy
    by_contra hys
    have he := fderiv_of_notMem_tsupport ℝ hys
    have hge : gradient ψ y=0 := by simp [gradient,he]
    simp [hge] at hy
  have hpot : Integrable (fun y ↦ q y*planeDivergence F y*φ y*ψ y) :=
    (((hq.continuous.mul (planeDivergence_continuous (hF.of_le (by simp)))).mul hφ.continuous).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross : Integrable (fun y ↦ fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) :=
    ((htest.continuous_fderiv (by simp)).clm_apply hF.continuous).integrable_of_hasCompactSupport
      (htestc.mono' (by
        intro y hy
        by_contra hn
        have he := fderiv_of_notMem_tsupport ℝ hn
        simp [he] at hy))
  have hpoint (y : Plane) :
      ⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫=
        (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫+
          fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y) := by
    rw [plane_gradient_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      plane_gradient_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y)]
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      fderiv_fun_mul ((hq.mul hφ).differentiable (by simp) y) (hψ.differentiable (by simp) y),
      fderiv_fun_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul]
    simp only [← inner_gradient_left,F]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  unfold graphJacobiForm
  rw [integral_sub hmain hpot]
  simp_rw [hpoint]
  rw [integral_add hmain hcross]
  have he : (∫ y,q y*planeDivergence F y*φ y*ψ y)=
      -(∫ y,fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) := by
    convert hibp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext y; ring
  rw [he,sub_neg_eq_add]

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcGraphJacobi_div_transform {g f ψ : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=
      ∫ y,⟪gradient f y,cmcJacobian (gradient g y)
        (gradient (fun z ↦ cmcWeight (gradient g z)*ψ z) y)⟫ := by
  have hp := plane_gradient_contDiff hg
  have hq := cmcWeight_contDiff.comp hp
  have he (y : Plane) : cmcWeight (gradient g y)*(f y/cmcWeight (gradient g y))=f y := by
    exact mul_div_cancel₀ _ (cmcWeight_pos _).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (gradient g y)) :=
    cmcJacobian_contDiff.comp hp
  have hq' : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcWeight (gradient g y)) := hq
  have hquot : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f y/cmcWeight (gradient g y)) :=
    hf.div hq (fun y ↦ (cmcWeight_pos _).ne')
  have ht := graphJacobiForm_transform hA
    (fun y v w ↦ (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _)) hq'
    hquot hψ hc
  have hefun : (fun z ↦ cmcWeight (gradient g z)*(f z/cmcWeight (gradient g z)))=f := funext he
  rw [hefun] at ht
  exact ht

theorem LinearCMCEquation.normal_jacobi {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆U) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=0 := by
  rw [cmcGraphJacobi_div_transform hg hf hψ hc]
  have hq := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  have hh := hw (fun y ↦ cmcWeight (gradient g y)*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  simp only [sub_zero,← inner_gradient_left] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  rw [cmcJacobian_symmetric,real_inner_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_graph_extension {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨fun y ↦ b y*g y,?_,?_⟩
  · exact contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  · intro y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

theorem WeakCMCGraph.coordinate_jacobi_chart {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (r : ℝ),0 < r ∧ r≤R ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      EqOn f g (Metric.ball 0 r) ∧
      (∀ i : Fin 2,LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
        (gradient f) (fun _ ↦ 0) (Metric.ball 0 r)) ∧
      ∀ i : Fin 2,∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 r →
        cmcGraphJacobi f (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)/
          cmcWeight (gradient f y)) ψ=0 := by
  obtain ⟨f,hfc,hfe⟩ := smooth_graph_extension hR hgc
  have he : f=ᶠ[𝓝 0]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Plane)∈Metric.ball 0 (R/2) by simp; linarith)] with y hy
    exact hfe hy
  have hgc0 : ContDiffAt ℝ (⊤ : ℕ∞) g 0 := hgc.contDiffAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hnear (i : Fin 2) : LinearCMCEquationNear
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f) (fun _ ↦ 0) := by
    have hh := hw.directional_linear_near hg hK hR (hgc.of_le (by simp))
      (ContDiffAt.holderJet (n := 2) (hgc0.of_le (by
        change ((3 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)))
      (EuclideanSpace.single i 1) (by simp)
    apply hh.congr
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ congrArg (fun L : Plane →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hy
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ by simp only [gradient,hy]
    · exact EventuallyEq.rfl
  obtain ⟨r0,hr0,h0⟩ := hnear 0
  obtain ⟨r1,hr1,h1⟩ := hnear 1
  let r := min (R/2) (min r0 r1)
  have hr : 0 < r := lt_min (by linarith) (lt_min hr0 hr1)
  have hrR : r≤R/2 := min_le_left _ _
  have hlin (i : Fin 2) : LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
      (gradient f) (fun _ ↦ 0) (Metric.ball 0 r) := by
    fin_cases i
    · exact h0.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))
    · exact h1.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨f,r,hr,by linarith,hfc,hfe.mono (Metric.ball_subset_ball hrR),hlin,?_⟩
  intro i ψ hψ hc hs
  exact (hlin i).normal_jacobi hfc
    ((hfc.fderiv_right (by simp)).clm_apply contDiff_const) hψ hc hs

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

lemma LinearCMCEquation.classical_zero {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hU : IsOpen U)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U) :
    ∀ y∈U,planeDivergence (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) y=0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) :=
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).clm_apply (plane_gradient_contDiff hf)
  have ht := classical_divergence_of_weak (H := 0) (hF.of_le (by simp)) hU
    (fun ψ hψ hc hs ↦ by simpa only [sub_zero,zero_mul] using hw ψ hψ hc hs)
  simpa only [neg_zero] using ht

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceNormalReverse
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma smooth_graph_extension_compact {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (K : ℝ≥0),ContDiff ℝ (⊤ : ℕ∞) f ∧
      HasCompactSupport f ∧ LipschitzWith K f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f : Plane → ℝ := fun y => b y*g y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hf.of_le (by simp)) hfc
  refine ⟨f,K,hf,hfc,hK,?_⟩
  intro y hy
  change b y*g y=g y
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

lemma smooth_graph_symbol_extension {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (p : Plane → Plane) (D : ℝ),ContDiff ℝ (⊤ : ℕ∞) p ∧
      (∀ y,‖p y‖≤1) ∧ 0≤D ∧ EqOn p (gradient g) (Metric.ball 0 (R/2)) ∧
      ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hgD : ContDiffOn ℝ (⊤ : ℕ∞) (gradient g) (Metric.ball 0 R) := by
    intro y hy
    have hd := (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)
    exact ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
      y hd).contDiffWithinAt
  let p : Plane → Plane := fun y => b y • gradient g y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hgD b.contDiff hs
  have hpc : HasCompactSupport p := b.hasCompactSupport.smul_right
  obtain ⟨C,hC⟩ := compact_C1_lipschitz (hp.of_le (by simp)) hpc
  have hpb (y : Plane) : ‖p y‖≤1 := by
    have hgrad : ‖gradient g y‖≤K := by
      simpa only [gradient,LinearIsometryEquiv.norm_map] using
        norm_fderiv_le_of_lipschitz ℝ hgL (x₀ := y)
    change ‖b y • gradient g y‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg (x := y))]
    exact ((mul_le_mul_of_nonneg_right (b.le_one (x := y)) (norm_nonneg _)).trans
      (by simpa using hgrad)).trans hK
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  refine ⟨p,L*C,hp,hpb,mul_nonneg hL C.coe_nonneg,?_,?_⟩
  · intro y hy
    change b y • gradient g y=gradient g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  · intro x y
    calc
      _ ≤ L*‖p x-p y‖ := hLip _ _ (hpb x) (hpb y)
      _ ≤ L*(C*dist x y) := mul_le_mul_of_nonneg_left
        (by simpa only [← dist_eq_norm] using hC.dist_le_mul x y) hL
      _ = _ := by ring

theorem WeakCMCGraph.smooth_jacobi_data {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R H : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (Kf : ℝ≥0) (p : Plane → Plane) (r D : ℝ),
      0 < r ∧ r≤R/2 ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      LipschitzWith Kf f ∧ EqOn f g (Metric.ball 0 (R/2)) ∧
      ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ y,‖p y‖≤1) ∧ 0≤D ∧
      EqOn p (gradient f) (Metric.ball 0 r) ∧
      (∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y) ∧
      ∀ i : Fin 2,LinearCMCEquation
        (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
        (fun _ => 0) (Metric.ball 0 r) := by
  obtain ⟨f,Kf,hf,hfc,hfL,hfg⟩ := smooth_graph_extension_compact hR hg
  obtain ⟨p,D,hp,hpb,hD,hpg,hpD⟩ := smooth_graph_symbol_extension hgL hK hR hg
  obtain ⟨f₀,r₀,hr₀,_,hf₀,hf₀g,hlin,_⟩ := hw.coordinate_jacobi_chart hgL hK hR hg
  let r := min (R/2) r₀
  have hr : 0 < r := lt_min (half_pos hR) hr₀
  have hrR : r≤R/2 := min_le_left _ _
  have hr0 : r ≤ r₀ := min_le_right _ _
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hrR hy)] with z hz
    exact hfg hz
  have he0 (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]f₀ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact (hfg (Metric.ball_subset_ball hrR hz)).trans
      (hf₀g (Metric.ball_subset_ball hr0 hz)).symm
  refine ⟨f,Kf,p,r,D,hr,hrR,hf,hfc,hfL,hfg,hp,hpb,hD,?_,hpD,?_⟩
  · intro y hy
    rw [hpg (Metric.ball_subset_ball hrR hy)]
    simp only [gradient,(he y hy).fderiv_eq]
  · intro i
    apply LinearCMCEquation.congr Metric.isOpen_ball
      ((hlin i).mono (Metric.ball_subset_ball hr0))
    · intro y hy
      exact congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (he0 y hy).fderiv_eq
    · intro y hy
      simp only [gradient,(he0 y hy).fderiv_eq]
    · intro y hy; rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_H1_jacobi_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0 < s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) s,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n x)=x) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (cubeCenter+normalGraph n f y))) 0 := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,hw,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,Kf,p,rj,D,hrj,hrjr,hf,hfc,hfL,hfg,hp,hpb,hD,hpf,hpD,hlin⟩ :=
    hw.smooth_jacobi_data hg (by norm_num) hr hgc
  have hf0 : f 0=0 := (hfg (Metric.mem_ball_self (half_pos hr))).trans hg0
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x (Metric.ball_subset_ball (by linarith) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (half_pos hr)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  have hext (x : Cover) (hx : x∈U) :
      graphSignedHeight cubeCenter n f x=graphSignedHeight cubeCenter n g x := by
    have hy : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      have hz : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR hx
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n (x-cubeCenter)).trans_lt (hz.trans hRr)
    simp only [graphSignedHeight,graphHeightExtension,hfg hy]
  have hphasef : (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ graphSignedHeight cubeCenter n f x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n f x)) := by
    rcases hphase with hphase|hphase
    · left; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
    · right; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  let χ := radialHeightCutoff cubeCenter (ρ/4)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := radialDensityWeight_contDiff _ _ _
  have hsχ : HasCompactSupport χ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hχs : tsupport χ⊆Metric.closedBall cubeCenter (ρ/2) := by
    have hh := radialDensityWeight_tsupport (a := cubeCenter)
      (by positivity : 0≤2*(ρ/4)) (by positivity : 0<3*(ρ/4)^2)
    convert hh using 1 <;> congr 1
    ring
  have hφχ (x : Cover) (hx : x∈tsupport χ) : φ x=1 :=
    radialHeightCutoff_one hρ (Metric.closedBall_subset_closedBall (by linarith) (hχs hx))
  have hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hχs.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans (hρU.trans hUO))
  have hΦ : Continuous (fun y => cubeCenter+normalGraph n f y) :=
    continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
      (hf.continuous.smul continuous_const))
  have hΦ0 : cubeCenter+normalGraph n f 0=cubeCenter := by
    simp only [normalGraph,hf0,zero_smul,add_zero]
    change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
    rw [map_zero,add_zero]
  have hnb : ∀ᶠ y in 𝓝 (0 : Plane),
      cubeCenter+normalGraph n f y∈Metric.ball cubeCenter (ρ/4) := by
    apply hΦ.continuousAt
    change Metric.ball cubeCenter (ρ/4)∈𝓝 (cubeCenter+normalGraph n f 0)
    rw [hΦ0]
    exact Metric.ball_mem_nhds _ (by positivity)
  obtain ⟨t,ht,htb⟩ := Metric.mem_nhds_iff.mp hnb
  let s := min rj t
  have hs : 0 < s := lt_min hrj ht
  have hsj : s ≤ rj := min_le_left _ _
  have hsr : s ≤ r/2 := hsj.trans hrjr
  have hunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      χ (cubeCenter+normalGraph n f y)=1 :=
    radialHeightCutoff_one (by positivity)
      (Metric.ball_subset_closedBall (htb (Metric.ball_subset_ball (min_le_right _ _) hy)))
  have hin (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
    have hy' := Metric.ball_subset_ball hsr hy
    simp only [normalGraph,hfg hy',quotientMap_add]
    exact hi y (Metric.ball_subset_ball (by linarith) hy')
  refine ⟨n,f,s,hn,hs,hf0,hf,hin,?_,?_⟩
  · intro x hx
    have hx' := Metric.ball_subset_ball hsr hx
    have hp' : normalPlaneCoordinates n x∈Metric.ball (0 : Plane) (r/2) := by
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n x).trans_lt
          (show ‖x‖ < r/2 from by simpa only [Metric.mem_ball,dist_zero_right] using hx')
    simpa only [normalGraph,hfg hp'] using hcover' x hx'
  · exact normalMeasure_H1_jacobi_signed_graph_smoothAt hE hμ N hN hae hu hhom
      cubeCenter hn hfL hf hphasef hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ
      hs hD hunit hp hpb (hpf.mono (Metric.ball_subset_ball hsj)) hpD
      (fun i => (hlin i).mono (Metric.ball_subset_ball hsj))
      (fun y hy => hNu _ (hin y hy)) hF hin hFu

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Translation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma normalTranslationLp_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    (p : ℝ≥0∞) [Fact (1≤p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F p (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslationLp μ a p u =ᵐ[(μ : Measure NormalBundle)] u ∘ translateNormal a :=
  Lp.coeFn_compMeasurePreserving u (translateNormal_measurePreserving μ a)

lemma gradient_smoothScalarTranslate (f : smoothPeriodicScalars) (a x : Cover) :
    gradient (smoothScalarTranslate f a).val x=gradient f.val (x+a) := by
  simp only [gradient,smoothScalarTranslate,fderiv_comp_add_right]

lemma smoothScalarTranslate_translate_value (f : smoothPeriodicScalars) (a : Cover) (z : NormalBundle) :
    smoothScalarValue (smoothScalarTranslate f a) (translateNormal a z)=smoothScalarValue f z := by
  change (smoothScalarTranslate f a).val (translateNormal a z).1=f.val z.1
  rw [translateNormal_periodic_eval (smoothScalarTranslate f a).property.2]
  change f.val ((z.1 : Cover)-a+a)=f.val z.1
  rw [sub_add_cancel]

lemma smoothScalarTranslate_translate_gradient (f : smoothPeriodicScalars) (a : Cover) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarTranslate f a) (translateNormal a z)=smoothScalarGradient f z := by
  have hp (m : Fin 3 → ℤ) (x : Cover) :
      gradient (smoothScalarTranslate f a).val (x+latticeVector m)=
        gradient (smoothScalarTranslate f a).val x := by
    simp only [gradient,fderiv_periodic (smoothScalarTranslate f a).property.2]
  have hg : gradient (smoothScalarTranslate f a).val (translateNormal a z).1=gradient f.val z.1 := by
    rw [translateNormal_periodic_eval hp,gradient_smoothScalarTranslate,sub_add_cancel]
  change gradient (smoothScalarTranslate f a).val (translateNormal a z).1-
    ⟪(z.2 : Cover),gradient (smoothScalarTranslate f a).val (translateNormal a z).1⟫ • (z.2 : Cover)=_
  rw [hg]
  rfl

lemma surfaceJetPullTranslation_smooth (μ : FiniteMeasure NormalBundle) (a : Cover)
    (f : smoothPeriodicScalars) :
    surfaceJetPullTranslation μ a (surfaceSmoothJet (μ.map (translateNormal a))
      (smoothScalarTranslate f a))=surfaceSmoothJet μ f := by
  apply Prod.ext
  · apply Lp.ext
    have ha := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarValue (smoothScalarTranslate f a)).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map (translateNormal a) : Measure NormalBundle))
    filter_upwards [normalTranslationLp_ae μ a 2
      (surfaceSmoothJet (μ.map (translateNormal a)) (smoothScalarTranslate f a)).1,ha,
      (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz ha hb
    exact hz.trans (ha.trans ((smoothScalarTranslate_translate_value f a z).trans hb.symm))
  · apply Lp.ext
    have ha := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarGradient (smoothScalarTranslate f a)).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map (translateNormal a) : Measure NormalBundle))
    filter_upwards [normalTranslationLp_ae μ a 2
      (surfaceSmoothJet (μ.map (translateNormal a)) (smoothScalarTranslate f a)).2,ha,
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz ha hb
    exact hz.trans (ha.trans ((smoothScalarTranslate_translate_gradient f a z).trans hb.symm))

lemma smoothScalarTranslate_neg_cancel (f : smoothPeriodicScalars) (a : Cover) :
    smoothScalarTranslate (smoothScalarTranslate f (-a)) a=f := by
  apply Subtype.ext
  funext x
  change f.val (x+a+ -a)=f.val x
  rw [add_neg_cancel_right]

lemma surfaceH1_translation_pull (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet (μ.map (translateNormal a))} (hu : u∈surfaceH1 (μ.map (translateNormal a))) :
    surfaceJetPullTranslation μ a u ∈ surfaceH1 μ := by
  apply map_mem_closure (surfaceJetPullTranslation μ a).continuous hu
  rintro _ ⟨f,rfl⟩
  refine ⟨smoothScalarTranslate f (-a),?_⟩
  have h := surfaceJetPullTranslation_smooth μ a (smoothScalarTranslate f (-a))
  rw [smoothScalarTranslate_neg_cancel] at h
  exact h.symm

theorem surfaceH1_translation_lift (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJetPullTranslation μ a v=u := by
  have hclosed : IsClosed ((surfaceJetPullTranslation μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) :=
    (surfaceJetPullTranslation μ a).isometry.isClosedEmbedding.isClosedMap _ isClosed_closure
  have hsub : Set.range (surfaceSmoothJet μ)⊆(surfaceJetPullTranslation μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a)))) := by
    rintro _ ⟨f,rfl⟩
    exact ⟨surfaceSmoothJet _ (smoothScalarTranslate f a),
      subset_closure (LinearMap.mem_range_self _ _),surfaceJetPullTranslation_smooth μ a f⟩
  exact closure_minimal hsub hclosed hu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjection_translate (a : Cover) (z : NormalBundle) :
    normalProjection (translateNormal a z)=normalProjection z-quotientMap a := by
  change quotientMap (representative (quotientMap z.1-quotientMap a))=_
  rw [quotientMap_representative]
  rfl

lemma normalTranslationLp_multiplier (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (u : Lp ℝ 2 (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslationLp μ a 2 (surfaceMultiplier (μ.map (translateNormal a)) q u)=
      surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u) := by
  apply Lp.ext
  have hm := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_lpSMul (r := 2) q u)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u),
    normalTranslationLp_ae μ a ∞ q,normalTranslationLp_ae μ a 2 u,
    normalTranslationLp_ae μ a 2 (surfaceMultiplier (μ.map (translateNormal a)) q u),hm]
      with z hz hq hu hv hm
  change (surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u)) z=_ at hz
  change surfaceMultiplier (μ.map (translateNormal a)) q u (translateNormal a z)=_ at hm
  simp only [Function.comp_apply,smul_eq_mul,Pi.mul_apply] at hz hq hu hv hm
  rw [hv,hm,hz,hq,hu]

lemma surfaceJacobiB_translation_pull (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (u v : SurfaceJet (μ.map (translateNormal a))) :
    surfaceJacobiB μ (normalTranslationLp μ a ∞ q)
      (surfaceJetPullTranslation μ a u) (surfaceJetPullTranslation μ a v)=
        surfaceJacobiB (μ.map (translateNormal a)) q u v := by
  change ⟪normalTranslationLp μ a 2 u.2,normalTranslationLp μ a 2 v.2⟫-
    ⟪surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u.1),
      normalTranslationLp μ a 2 v.1⟫=_
  rw [← normalTranslationLp_multiplier,
    (normalTranslationLp μ a 2 (F := Cover)).inner_map_map u.2 v.2,
    (normalTranslationLp μ a 2 (F := ℝ)).inner_map_map
      (surfaceMultiplier (μ.map (translateNormal a)) q u.1) v.1]
  rfl

lemma surfaceCurvatureLp_translation (μ : FiniteMeasure NormalBundle) (a : Cover)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    normalTranslationLp μ a ∞
      (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
        (hN.comp (contDiff_id.add contDiff_const)))=surfaceCurvatureLp μ N hN := by
  apply Lp.ext
  let Q : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩
  let Q' : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous (N := fun x => N (x+a))
      (hN.comp (contDiff_id.add contDiff_const))).comp
      (continuous_subtype_val.comp continuous_fst)⟩
  have hqp (m : Fin 3 → ℤ) (x : Cover) :
      coverTrace ((fderiv ℝ N (x+latticeVector m+a)).comp (fderiv ℝ N (x+latticeVector m+a)))=
        coverTrace ((fderiv ℝ N (x+a)).comp (fderiv ℝ N (x+a))) := by
    rw [add_right_comm,fderiv_periodic hp]
  have he (z : NormalBundle) : Q' (translateNormal a z)=Q z := by
    change coverTrace ((fderiv ℝ (fun x => N (x+a)) (translateNormal a z).1).comp
      (fderiv ℝ (fun x => N (x+a)) (translateNormal a z).1))=_
    simp only [fderiv_comp_add_right]
    rw [translateNormal_periodic_eval (F := fun x =>
      coverTrace ((fderiv ℝ N (x+a)).comp (fderiv ℝ N (x+a)))) hqp,sub_add_cancel]
    rfl
  have hq := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
    (Q'.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ.map (translateNormal a) : Measure NormalBundle))
  filter_upwards [normalTranslationLp_ae μ a ∞
    (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
      (hN.comp (contDiff_id.add contDiff_const))),hq,
    Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz hq hr
  exact hz.trans (hq.trans ((he z).trans hr.symm))

theorem surfaceH1_jacobi_translation_lift (μ : FiniteMeasure NormalBundle) (a : Cover)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hh : ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) :
    ∃ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJetPullTranslation μ a v=u ∧
      ∀ w∈surfaceH1 (μ.map (translateNormal a)),
        surfaceJacobiB (μ.map (translateNormal a))
          (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
            (hN.comp (contDiff_id.add contDiff_const))) v w=0 := by
  obtain ⟨v,hv,he⟩ := surfaceH1_translation_lift μ a hu
  refine ⟨v,hv,he,?_⟩
  intro w hw
  rw [← surfaceJacobiB_translation_pull,surfaceCurvatureLp_translation μ a N hN hp,he]
  exact hh _ (surfaceH1_translation_pull μ a hw)

lemma surfaceH1_translation_value (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} {v : SurfaceJet (μ.map (translateNormal a))}
    (he : surfaceJetPullTranslation μ a v=u)
    {F : Torus → ℝ} (hF : Measurable F)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    (v.1 : NormalBundle → ℝ)=ᵐ[(μ.map (translateNormal a) : Measure NormalBundle)]
      (fun x => F (x+quotientMap a)) ∘ normalProjection := by
  change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),
    v.1 z=F (normalProjection z+quotientMap a)
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable v.1).measurable
      (hF.comp (normalProjection_continuous.measurable.add measurable_const)))).mpr
  have hs := normalTranslationLp_ae μ a 2 v.1
  have he1 : normalTranslationLp μ a 2 v.1=u.1 := congrArg Prod.fst he
  rw [he1] at hs
  filter_upwards [hs,hFu] with z hz hf
  simp only [Function.comp_apply] at hz hf
  change v.1 (translateNormal a z)=F (normalProjection (translateNormal a z)+quotientMap a)
  rw [← hz,hf,normalProjection_translate,sub_add_cancel]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_H1_jacobi_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0 < s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ z∈Metric.ball (0 : Cover) s,
        quotientMap (x+z)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n z)=z) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+normalGraph n f y))) 0 := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have he (z : Cover) : cubeCenter+z+a=x+z := by dsimp [a]; abel
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [a]; congr 1; abel
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
  have hNu' (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E')) :
      ∀ᶠ z in 𝓝 y,‖N' z‖=1 := by
    rw [frontier_openRepresentative_translation hE] at hy
    have hy' : quotientMap (y+a)∈frontier (openRepresentative E) := by
      simpa only [mem_preimage,quotientMap_add] using hy
    exact (continuous_add_const a).continuousAt.eventually (hNu (y+a) hy')
  let F' : Torus → ℝ := fun z => F (z+quotientMap a)
  have hF' : ContinuousOn F' (frontier (openRepresentative E')) := by
    apply hF.comp (continuous_add_const _).continuousOn
    intro z hz
    rwa [frontier_openRepresentative_translation hE] at hz
  obtain ⟨v,hv,hpull,hvh⟩ := surfaceH1_jacobi_translation_lift μ a N hN hp hu hhom
  have hvF : (v.1 : NormalBundle → ℝ)=ᵐ[(μ.map (translateNormal a) : Measure NormalBundle)]
      F' ∘ normalProjection := surfaceH1_translation_value μ a hpull hFm hFu
  obtain ⟨n,f,s,hn,hs,hf0,hf,hin,hcover,hreg⟩ :=
    isMinimizerAt_centered_H1_jacobi_smooth hV hE' hmin' hc
      (isNormalMeasure_translation hE hμ a) N' hN' hae' hNu' hv hvh hF' hvF
  refine ⟨n,f,s,hn,hs,hf0,hf,?_,?_,?_⟩
  · intro y hy
    have hi := hin y hy
    rw [frontier_openRepresentative_translation hE] at hi
    simpa only [mem_preimage,← quotientMap_add,he] using hi
  · intro z hz
    have hc' := hcover z hz
    rw [frontier_openRepresentative_translation hE] at hc'
    simpa only [mem_preimage,← quotientMap_add,he] using hc'
  · simpa only [F',← quotientMap_add,he] using hreg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_line_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) (t : ℝ) :
    deriv (fun s : ℝ => f (x+s • v)) t= fderiv ℝ f (x+t • v) v := by
  simpa only [Function.comp_def,id_eq,one_smul] using ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const v |>.const_add x)).deriv

lemma smooth_line_second_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) :
    deriv (deriv (fun s : ℝ => f (x+s • v))) 0=
      ⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have he : deriv (fun s : ℝ => f (x+s • v))=
      (fun t => fderiv ℝ f (x+t • v) v) := funext (smooth_line_deriv hf x v)
  rw [he]
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) :=
    hf.fderiv_right (by simp) |>.clm_apply contDiff_const
  rw [smooth_line_deriv hg x v 0]
  simp only [zero_smul,add_zero]
  rw [plane_hessian_direction hf,inner_gradient_left]

lemma plane_hessian_nonneg_of_local_min {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane} (hm : IsLocalMin f x) (v : Plane) :
    0≤⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (show Continuous (fun t : ℝ => x+t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
  have hm' : IsLocalMin (fun t : ℝ => f (x+t • v)) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), f (x+0 • v)≤f (x+t • v)
    simpa only [zero_smul,add_zero] using ht.eventually hm
  rw [← smooth_line_second_deriv hf x v]
  exact second_derivative_nonneg_of_local_min hm'
    (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt

lemma planeFrameOperator_nonneg_of_local_min (B : Plane → Fin 2 → Plane)
    (b : Plane → Plane) {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} (hm : IsLocalMin f x) : 0≤planeFrameOperator B b f x := by
  have hz : gradient f x=0 := by simp [gradient,hm.fderiv_eq_zero]
  simp only [planeFrameOperator,hz,inner_zero_left,add_zero]
  exact Finset.sum_nonneg (fun i _ => plane_hessian_nonneg_of_local_min hf hm (B x i))

lemma planeFrameOperator_sub (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f g : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Plane) : planeFrameOperator B b (fun y => f y-g y) x=
      planeFrameOperator B b f x-planeFrameOperator B b g x := by
  have he : gradient (fun y => f y-g y)=fun y => gradient f y-gradient g y := by
    funext y
    simp only [gradient,fderiv_fun_sub (hf.differentiable (by simp) y)
      (hg.differentiable (by simp) y),map_sub]
  rw [planeFrameOperator,he,fderiv_fun_sub
    ((plane_gradient_contDiff hf).differentiable (by simp) x)
    ((plane_gradient_contDiff hg).differentiable (by simp) x)]
  simp only [sub_apply,inner_sub_left,Finset.sum_sub_distrib,planeFrameOperator]
  ring

lemma planeFrameOperator_smul (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x : Plane) :
    planeFrameOperator B b (fun y => c*f y) x=c*planeFrameOperator B b f x := by
  have he : gradient (fun y => c*f y)=fun y => c • gradient f y := by
    funext y
    simp only [gradient,show (fun y => c*f y)=(fun y => c • f y) from rfl,
      fderiv_fun_const_smul (hf.differentiable (by simp) y),map_smul]
  rw [planeFrameOperator,he,fderiv_fun_const_smul
    ((plane_gradient_contDiff hf).differentiable (by simp) x)]
  simp only [smul_apply,real_inner_smul_left,← Finset.mul_sum,planeFrameOperator]
  ring

theorem planeFrameOperator_annulus_comparison (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : Plane) {r R : ℝ} (hr : 0 < r) (hrR : r<R)
    (hbd : ∀ x,‖x-c‖=r ∨ ‖x-c‖=R → 0≤f x)
    (hL : ∀ x,r<‖x-c‖ → ‖x-c‖<R → planeFrameOperator B b f x<0) :
    ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤f x := by
  let K : Set Plane := Metric.closedBall c R \ Metric.ball c r
  have hK : IsCompact K := (isCompact_closedBall c R).diff Metric.isOpen_ball
  have hKne : K.Nonempty := by
    obtain ⟨point,hpoint⟩ := (NormedSpace.sphere_nonempty (x := c)).2 hr.le
    have hdist : dist point c=r := hpoint
    refine ⟨point,?_⟩
    change dist point c≤R ∧ ¬ dist point c < r
    rw [hdist]
    exact ⟨hrR.le,lt_irrefl r⟩
  intro x hrx hxR
  have hxK : x∈K := by simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,
    not_lt] using And.intro hxR hrx
  obtain ⟨y,hyK,hym⟩ := hK.exists_isMinOn hKne hf.continuous.continuousOn
  have hyr : r≤‖y-c‖ := by simpa only [K,Set.mem_sdiff,Metric.mem_ball,dist_eq_norm,not_lt] using hyK.2
  have hyR : ‖y-c‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hyK.1
  have hy0 : 0≤f y := by
    by_cases h1 : ‖y-c‖=r
    · exact hbd y (Or.inl h1)
    by_cases h2 : ‖y-c‖=R
    · exact hbd y (Or.inr h2)
    have hri : r<‖y-c‖ := lt_of_le_of_ne hyr (Ne.symm h1)
    have hRi : ‖y-c‖<R := lt_of_le_of_ne hyR h2
    have hn : K∈𝓝 y := by
      have ho : IsOpen {z : Plane | r<‖z-c‖ ∧ ‖z-c‖<R} :=
        (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
      apply mem_of_superset (ho.mem_nhds ⟨hri,hRi⟩)
      intro z hz
      simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,not_lt] using
        And.intro hz.2.le hz.1.le
    have hm : IsLocalMin f y := hym.isLocalMin hn
    exact False.elim ((not_lt_of_ge (planeFrameOperator_nonneg_of_local_min B b hf hm))
      (hL y hri hRi))
  exact hy0.trans (hym hxK)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneQuadraticWeight
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

lemma planeHopfBarrier_smooth (c : Plane) (α R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeHopfBarrier c α R) :=
  ((contDiff_const.mul (((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => x)).sub contDiff_const).norm_sq ℝ)).exp).sub contDiff_const

lemma planeHopfBarrier_fderiv (c : Plane) (α R : ℝ) (x : Plane) :
    fderiv ℝ (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • innerSL ℝ (x-c) := by
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp.sub_const
    (Real.exp (-α*R^2))
  change fderiv ℝ (fun x => Real.exp (-α*‖x-c‖^2)-Real.exp (-α*R^2)) x=_
  simp only [id_eq] at h
  rw [h.fderiv]
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma planeHopfBarrier_gradient (c : Plane) (α R : ℝ) (x : Plane) :
    gradient (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • (x-c) := by
  ext i
  rw [plane_gradient_component,planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,smul_eq_mul,PiLp.smul_apply]

lemma planeHopfBarrier_hessian (c : Plane) (α R : ℝ) (x v : Plane) :
    ⟪fderiv ℝ (gradient (planeHopfBarrier c α R)) x v,v⟫=
      Real.exp (-α*‖x-c‖^2)*(4*α^2*⟪x-c,v⟫^2-2*α*‖v‖^2) := by
  have he : gradient (planeHopfBarrier c α R)=
      fun y => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c) :=
    funext (planeHopfBarrier_gradient c α R)
  rw [he]
  have hd := (((((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp).const_mul (-2*α)).smul
    ((hasFDerivAt_id x).sub_const c)
  simp only [id_eq] at hd
  change HasFDerivAt (fun y : Plane => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

lemma planeFrameOperator_barrier (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) (α R : ℝ) (x : Plane) :
    planeFrameOperator B b (planeHopfBarrier c α R) x=
      Real.exp (-α*‖x-c‖^2)*
        (4*α^2*(∑ i,⟪x-c,B x i⟫^2)-2*α*(∑ i,‖B x i‖^2)-2*α*⟪x-c,b x⟫) := by
  simp only [planeFrameOperator,planeHopfBarrier_hessian,planeHopfBarrier_gradient,
    real_inner_smul_left,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma planeFrameOperator_barrier_pos (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) {α R r κ K : ℝ} (hr : 0 < r) (hκ : 0<κ) (hK : 0≤K)
    (hα : 0<α) (hlarge : K*(1+R)<2*α*κ*r^2)
    {x : Plane} (hrx : r≤‖x-c‖) (hxR : ‖x-c‖≤R)
    (hell : κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2)
    (hB : (∑ i,‖B x i‖^2)≤K) (hb : ‖b x‖≤K) :
    0<planeFrameOperator B b (planeHopfBarrier c α R) x := by
  rw [planeFrameOperator_barrier]
  apply mul_pos (Real.exp_pos _) ?_
  have hb' : ⟪x-c,b x⟫≤R*K := (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hxR hK))
  have hsq : r^2≤‖x-c‖^2 := sq_le_sq₀ hr.le (norm_nonneg _) |>.mpr hrx
  have he : κ*r^2≤∑ i,⟪x-c,B x i⟫^2 :=
    (mul_le_mul_of_nonneg_left hsq hκ.le).trans hell
  have ha2 : 0<2*α := by positivity
  have ha4 : 0≤4*α^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left he ha4
  have h2 := mul_le_mul_of_nonneg_left hB ha2.le
  have h3 := mul_le_mul_of_nonneg_left hb' ha2.le
  have h4 := mul_lt_mul_of_pos_left hlarge ha2
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma deriv_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),f 0≤f t) : 0≤d := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  apply ge_of_tendsto ht
  filter_upwards [hm,self_mem_nhdsWithin] with t hmt ht
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr hmt) (by simpa using (show 0≤t from le_of_lt ht))

lemma planeHopfBarrier_inward (c : Plane) {α R : ℝ} (hα : 0<α) (hR : 0<R)
    {y : Plane} (hy : ‖y-c‖=R) :
    0<fderiv ℝ (planeHopfBarrier c α R) y (c-y) := by
  rw [planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul]
  have hi : ⟪y-c,c-y⟫= -R^2 := by
    rw [show c-y= -(y-c) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hy]
  rw [hi]
  have hp : 0<2*α*Real.exp (-α*‖y-c‖^2)*R^2 := by positivity
  nlinarith

theorem planeFrameOperator_hopf (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (c : Plane) {R κ K : ℝ} (hR : 0<R) (hκ : 0<κ) (hK : 0≤K)
    (hcoeff : ∀ x,R/2≤‖x-c‖ → ‖x-c‖≤R →
      κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2 ∧
        (∑ i,‖B x i‖^2)≤K ∧ ‖b x‖≤K)
    (hL : ∀ x,‖x-c‖<R → planeFrameOperator B b u x≤0)
    (hpos : ∀ x,‖x-c‖<R → 0<u x)
    {y : Plane} (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrR : r<R := half_lt_self hR
  have hbound : ∀ x,‖x-c‖≤R → 0≤u x := by
    have hs : Metric.ball c R⊆{x | 0≤u x} := by
      intro x hx
      exact (hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)).le
    have hc := closure_minimal hs (isClosed_le continuous_const hu.continuous)
    rw [closure_ball c hR.ne'] at hc
    intro x hx
    exact hc (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  obtain ⟨z,hz,hzmin⟩ := (isCompact_closedBall c r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) hu.continuous.continuousOn
  have hzr : ‖z-c‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  let δ := u z
  have hδ : 0<δ := hpos z (hzr.trans_lt hrR)
  let α := (K*(1+R)+1)/(2*κ*r^2)
  have hα : 0<α := by dsimp [α]; positivity
  have hlarge : K*(1+R)<2*α*κ*r^2 := by
    have he : 2*α*κ*r^2=K*(1+R)+1 := by
      dsimp [α]; field_simp
    rw [he]; linarith
  let φ := planeHopfBarrier c α R
  have hφ := planeHopfBarrier_smooth c α R
  have hφle (x : Plane) : φ x≤1 := by
    have he : Real.exp (-α*‖x-c‖^2)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (sq_nonneg _))
    dsimp [φ,planeHopfBarrier]
    linarith [Real.exp_pos (-α*R^2)]
  have hφzero (x : Plane) (hx : ‖x-c‖=R) : φ x=0 := by simp only [φ,planeHopfBarrier,hx,sub_self]
  have hcomp : ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤u x-δ*φ x := by
    apply planeFrameOperator_annulus_comparison B b (hu.sub (contDiff_const.mul hφ)) c hr hrR
    · intro x hx
      change 0≤u x-δ*φ x
      rcases hx with hx|hx
      · have hzle : δ≤u x := hzmin (by simpa only [Metric.mem_closedBall,dist_eq_norm,hx] using (le_refl r))
        have hh := mul_le_mul_of_nonneg_left (hφle x) hδ.le
        nlinarith
      · rw [hφzero x hx,mul_zero,sub_zero]
        exact hbound x hx.le
    · intro x hrx hxR
      rw [planeFrameOperator_sub B b hu (contDiff_const.mul hφ),
        planeFrameOperator_smul B b hφ]
      have hc := hcoeff x hrx.le hxR.le
      have hbar := planeFrameOperator_barrier_pos B b c hr hκ hK hα hlarge
        hrx.le hxR.le hc.1 hc.2.1 hc.2.2
      exact sub_neg.mpr ((hL x hxR).trans_lt (mul_pos hδ hbar))
  let g : ℝ → ℝ := fun t => u (y+t • (c-y))-δ*φ (y+t • (c-y))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (hu.sub (contDiff_const.mul hφ)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg0 : g 0=0 := by simp only [g,zero_smul,add_zero,huy,hφzero y hy,mul_zero,sub_self]
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),g 0≤g t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with t ht hth
    have ht0 : 0<t := ht
    have hnorm : ‖y+t • (c-y)-c‖=(1-t)*R := by
      rw [show y+t • (c-y)-c=(1-t) • (y-c) by module,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith),hy]
    rw [hg0]
    apply hcomp
    · rw [hnorm]; dsimp [r]; nlinarith
    · rw [hnorm]; nlinarith
  have hd := deriv_nonneg_of_right_min (hg.differentiable (by simp) 0).hasDerivAt hm
  have he : deriv g 0=fderiv ℝ u y (c-y)-δ*fderiv ℝ φ y (c-y) := by
    have hl := smooth_line_deriv (hu.sub ((contDiff_const (c := δ)).mul hφ)) y (c-y) 0
    change deriv g 0=_ at hl
    rw [hl]
    simp only [zero_smul,add_zero]
    rw [fderiv_fun_sub (hu.differentiable (by simp) y)
      ((contDiff_const.mul hφ).differentiable (by simp) y),
      fderiv_const_mul (hφ.differentiable (by simp) y)]
    simp [φ]

  rw [he] at hd
  exact (mul_pos hδ (planeHopfBarrier_inward c hα hR hy)).trans_le (sub_nonneg.mp hd)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CMCFrameOperator
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem plane_interior_ball_at_frontier {D : Set Plane} (hD : IsOpen D)
    {a : Plane} (ha : a∈frontier D) {ε : ℝ} (hε : 0<ε) :
    ∃ (c y : Plane) (R : ℝ),0<R ∧
      Metric.ball c R⊆D ∧ ‖y-c‖=R ∧ y∈frontier D ∧
      Metric.closedBall c R⊆Metric.ball a ε := by
  have hac : a∈closure D := frontier_subset_closure ha
  have had : a∉D := by
    rw [frontier, hD.interior_eq] at ha
    exact ha.2
  obtain ⟨c,hcD,hca⟩ := Metric.mem_closure_iff.mp hac (ε/4) (by positivity)
  have hcomp : Dᶜ.Nonempty := ⟨a,had⟩
  let R := Metric.infDist c Dᶜ
  have hR : 0<R := (hD.isClosed_compl.notMem_iff_infDist_pos hcomp).mp (by simpa using hcD)
  have hRa : R≤dist c a := Metric.infDist_le_dist_of_mem had
  obtain ⟨y,hyc,hRy⟩ := hD.isClosed_compl.exists_infDist_eq_dist hcomp c
  have hball : Metric.ball c R⊆D := Metric.ball_infDist_compl_subset
  have hyR : ‖y-c‖=R := by
    rw [← dist_eq_norm,dist_comm]
    exact hRy.symm
  have hycl : y∈closure D := by
    apply closure_mono hball
    rw [closure_ball c hR.ne']
    simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)
  refine ⟨c,y,R,hR,hball,hyR,?_,?_⟩
  · rw [frontier,hD.interior_eq]
    exact ⟨hycl,hyc⟩
  · intro z hz
    have hzR : dist z c≤R := hz
    have hca' : dist c a<ε/4 := by simpa only [dist_comm] using hca
    have hza := dist_triangle z c a
    change dist z a<ε
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_symbol {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) {u : Plane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeDivergence (fun z => A z (gradient u z)) x=
      planeTrace ((A x).comp (fderiv ℝ (gradient u) x))+
        ⟪gradient u x,planeSymbolDrift A x⟫ := by
  have hda := (hA.differentiable (by simp) x).hasFDerivAt
  have hdu := ((plane_gradient_contDiff hu).differentiable (by simp) x).hasFDerivAt
  have hprod := hda.clm_apply hdu
  have hc (j : Fin 2) := hda.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  simp only [planeSymbolDrift,planeDivergence,planeTrace]
  rw [hprod.fderiv]
  simp_rw [(hc _).fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_zero,
    Fin.sum_univ_two,inner_add_right,real_inner_smul_right,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.add_apply]
  rw [plane_decompose (gradient u x)]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    PiLp.single_apply,ite_true,mul_one]
  norm_num
  ring

lemma cmc_compress_hessian_trace (p : Plane) (L : Plane →L[ℝ] Plane) :
    (∑ i : Fin 2,⟪L (cmcCompress p (EuclideanSpace.single i 1)),
      cmcCompress p (EuclideanSpace.single i 1)⟫)=
      cmcWeight p*planeTrace ((cmcJacobian p).comp L) := by
  calc
    _ = planeTrace ((cmcCompress p).comp (L.comp (cmcCompress p))) := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,← cmcCompress_symm,
        EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    _ = planeTrace ((L.comp (cmcCompress p)).comp (cmcCompress p)) := planeTrace_comp_comm _ _
    _ = planeTrace (L.comp ((cmcCompress p).comp (cmcCompress p))) := by rfl
    _ = planeTrace (((cmcCompress p).comp (cmcCompress p)).comp L) := planeTrace_comp_comm _ _
    _ = _ := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,cmcCompress_sq,PiLp.smul_apply,
        smul_eq_mul,← Finset.mul_sum]

lemma cmc_frame_operator {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeFrameOperator (fun y i => cmcCompress (gradient g y) (EuclideanSpace.single i 1))
      (fun y => cmcWeight (gradient g y) •
        planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x=
      cmcWeight (gradient g x)*planeDivergence
        (fun y => cmcJacobian (gradient g y) (gradient u y)) x := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z => cmcJacobian (gradient g z)) :=
    cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  rw [planeDivergence_symbol hA hu]
  simp only [planeFrameOperator,cmc_compress_hessian_trace,real_inner_smul_right]
  ring

lemma cmc_frame_ellipticity {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/4 : ℝ)*‖v‖^2≤∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2 := by
  have he : (∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2)=‖cmcCompress p v‖^2 := by
    simp only [← cmcCompress_symm,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [he]
  have hh := cmcStretch_norm hp (cmcCompress p v)
  rw [cmcStretch_compress] at hh
  nlinarith [norm_nonneg (cmcCompress p v),norm_nonneg v]

lemma cmc_frame_bound {p : Plane} (hp : ‖p‖≤1) :
    (∑ i : Fin 2,‖cmcCompress p (EuclideanSpace.single i 1)‖^2)≤8 := by
  have hh (i : Fin 2) : ‖cmcCompress p (EuclideanSpace.single i 1)‖≤2 := by
    simpa using cmcCompress_norm hp (EuclideanSpace.single i 1)
  rw [Fin.sum_univ_two]
  nlinarith [hh 0,hh 1,norm_nonneg (cmcCompress p (EuclideanSpace.single 0 1)),
    norm_nonneg (cmcCompress p (EuclideanSpace.single 1 1))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeSymbolDrift_continuous {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) : Continuous (planeSymbolDrift A) := by
  unfold planeSymbolDrift
  apply continuous_finsetSum
  intro i _
  exact (planeDivergence_continuous ((hA.clm_apply contDiff_const).of_le (by simp))).smul continuous_const

theorem LinearCMCEquation.hopf {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R : ℝ} (hR : 0<R)
    (hp : ∀ x∈Metric.closedBall c R,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball c R))
    (hpos : ∀ x∈Metric.ball c R,0<u x)
    (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let A : Plane → Plane →L[ℝ] Plane := fun x => cmcJacobian (gradient g x)
  let b : Plane → Plane := fun x => cmcWeight (gradient g x) • planeSymbolDrift A x
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  have hb : Continuous b := (cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).continuous.smul
    (planeSymbolDrift_continuous hA)
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hb.continuousOn
  let K := max 8 (max C 0)
  have hK8 : 8≤K := le_max_left _ _
  have hKC : C≤K := (le_max_left C 0).trans (le_max_right _ _)
  have hK : 0≤K := (le_max_right C 0).trans (le_max_right _ _)
  apply planeFrameOperator_hopf
    (fun x i => cmcCompress (gradient g x) (EuclideanSpace.single i 1)) b hu c hR
    (by norm_num : 0<(1/4 : ℝ)) hK ?_ ?_ ?_ hy huy
  · intro x _ hxR
    have hx : x∈Metric.closedBall c R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hxR
    exact ⟨cmc_frame_ellipticity (hp x hx) (x-c),
      (cmc_frame_bound (hp x hx)).trans hK8,(hC x hx).trans hKC⟩
  · intro x hx
    change planeFrameOperator _ (fun y => cmcWeight (gradient g y) •
      planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x≤0
    rw [cmc_frame_operator hg hu,hw.classical_zero hg hu Metric.isOpen_ball x
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hx),mul_zero]
  · intro x hx
    exact hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.affine_zero {u v : Plane → ℝ} {p : Plane → Plane}
    {U : Set Plane} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : Continuous p)
    (hue : LinearCMCEquation u p (fun _ => 0) U)
    (hve : LinearCMCEquation v p (fun _ => 0) U) (c a b : ℝ) :
    LinearCMCEquation (fun y => c+a*u y+b*v y) p (fun _ => 0) U := by
  have hg (y : Plane) : gradient (fun z => c+a*u z+b*v z) y=
      a • gradient u y+b • gradient v y := by
    have hd := ((hasFDerivAt_const c y).add
      ((hu.differentiable (by simp) y).hasFDerivAt.const_mul a)).add
        ((hv.differentiable (by simp) y).hasFDerivAt.const_mul b)
    have he : fderiv ℝ (fun z => c+a*u z+b*v z) y=
        0+a • fderiv ℝ u y+b • fderiv ℝ v y := hd.fderiv
    simp only [gradient,he,zero_add,map_add,map_smul]
  intro ψ hψ hc hs
  have hi (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
      Integrable (fun y => fderiv ℝ ψ y (cmcJacobian (p y) (gradient w y))) := by
    apply ((hψ.continuous_fderiv (by simp)).clm_apply
      ((cmcJacobian_contDiff.continuous.comp hp).clm_apply
        (plane_gradient_contDiff hw).continuous)).integrable_of_hasCompactSupport
    apply (hc.fderiv ℝ).mono
    intro y hy hz
    exact hy (by simp only [hz,zero_apply])
  simp_rw [hg,sub_zero,map_add,map_smul,smul_eq_mul]
  rw [integral_add ((hi u hu).const_mul a) ((hi v hv).const_mul b),
    integral_const_mul,integral_const_mul]
  have hu0 := hue ψ hψ hc hs
  have hv0 := hve ψ hψ hc hs
  simp only [sub_zero] at hu0 hv0
  rw [hu0,hv0,mul_zero,mul_zero,add_zero]

lemma normalTranslationNumerator_contDiff (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalTranslationNumerator n g v σ) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_const.inner ℝ (plane_gradient_contDiff hg)))

lemma normalTranslationNumerator_eq (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : normalTranslationNumerator n g v σ y=
      σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
        fderiv ℝ g y (EuclideanSpace.single 0 1)+
      (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1) := by
  simp only [normalTranslationNumerator,plane_inner_components,plane_gradient_component]
  ring

lemma normalTranslationNumerator_linear (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) {U : Set Plane}
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) U) :
    LinearCMCEquation (normalTranslationNumerator n g v σ) (gradient g) (fun _ => 0) U := by
  simp_rw [show normalTranslationNumerator n g v σ = fun y =>
    σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
      fderiv ℝ g y (EuclideanSpace.single 0 1)+
    (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1)
      from funext (normalTranslationNumerator_eq n g v σ)]
  exact (hlin 0).affine_zero
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    (plane_gradient_contDiff hg).continuous (hlin 1) _ _ _

lemma normalTranslationNumerator_weight {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (v : Cover) (σ : ℝ) (y : Plane) :
    normalTranslationNumerator n g v σ y=
      cmcWeight (gradient g y)*⟪v,σ • graphSlopeNormal n (gradient g y)⟫ := by
  rw [graphSlopeNormal_weight hn]
  simp only [normalTranslationNumerator,inner_smul_right,inner_sub_right]
  have he : ⟪normalPlaneCoordinates n v,gradient g y⟫=
      ⟪v,normalPlaneEmbedding n (gradient g y)⟫ :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [he]
  field_simp [(cmcWeight_pos (gradient g y)).ne']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma contDiffAt_occupied_graph_transition {S : Set Torus} {F : Torus → ℝ}
    {x : Cover} {G : Plane → Cover} {a : Plane}
    (hG : ContDiffAt ℝ (⊤ : ℕ∞) G a)
    (hGS : ∀ᶠ y in 𝓝 a,quotientMap (x+G y)∈S)
    {n : Cover} {f : Plane → ℝ} {s : ℝ} (hs : 0 < s)
    (hcover : ∀ z∈Metric.ball (0 : Cover) s,
      quotientMap ((x+G a)+z)∈S → normalGraph n f (normalPlaneCoordinates n z)=z)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => F (quotientMap ((x+G a)+normalGraph n f y))) 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+G y))) a := by
  let P : Plane → Plane := fun y => normalPlaneCoordinates n (G y-G a)
  have hP : ContDiffAt ℝ (⊤ : ℕ∞) P a :=
    (normalPlaneCoordinates n).contDiff.contDiffAt.comp a (hG.sub contDiffAt_const)
  have hP0 : P a=0 := by simp [P]
  have hF' : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => F (quotientMap ((x+G a)+normalGraph n f y))) (P a) := by
    rw [hP0]; exact hF
  have hcomp := hF'.comp a hP
  apply hcomp.congr_of_eventuallyEq
  have ht : Tendsto (fun y => G y-G a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : ContinuousAt (fun y => G y-G a) a := hG.continuousAt.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [hGS,ht.eventually (Metric.ball_mem_nhds _ hs)] with y hy hys
  have hy' : quotientMap ((x+G a)+(G y-G a))∈S := by
    convert hy using 1; congr 1; abel
  have he := hcover (G y-G a) hys hy'
  change F (quotientMap (x+G y))=F (quotientMap ((x+G a)+normalGraph n f (P y)))
  rw [show normalGraph n f (P y)=G y-G a from he]
  congr 2
  abel

theorem isMinimizerAt_H1_jacobi_parametric_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (x : Cover) {G : Plane → Cover} {a : Plane}
    (hG : ContDiffAt ℝ (⊤ : ℕ∞) G a)
    (hGS : ∀ᶠ y in 𝓝 a,quotientMap (x+G y)∈frontier (openRepresentative E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+G y))) a := by
  obtain ⟨n,f,s,_,hs,_,_,_,hc,hr⟩ := isMinimizerAt_H1_jacobi_smooth
    hV hE hmin hμ N hN hp hae hNu hu hhom hFm hF hFu (x+G a) hGS.self_of_nhds
  exact contDiffAt_occupied_graph_transition hG hGS hs (fun z hz => (hc z hz).mp) hr

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotient_graph_closure {S D : Set Torus} (hDS : D⊆S)
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hx : quotientMap x∈closure D) :
    (0 : Plane)∈closure ((fun y => quotientMap (x+G y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball (0 : Plane) ε := by
    have ht : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
      simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
    exact ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hcover.and hP)
  obtain ⟨a,haD,hax⟩ := Metric.mem_closure_iff.mp hx δ hδ
  have ha : a∈Metric.ball (quotientMap x) δ := by
    simpa only [Metric.mem_ball,dist_comm] using hax
  rw [← quotientMap_image_ball x δ] at ha
  obtain ⟨z,hzx,hza⟩ := ha
  have hz : z-x∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hzx
  obtain ⟨hi,hp⟩ := hsub hz
  have hzs : quotientMap (x+(z-x))∈S := by
    simpa only [add_sub_cancel,hza] using hDS haD
  refine ⟨P (z-x),?_,?_⟩
  · change quotientMap (x+G (P (z-x)))∈D
    rw [hi hzs,add_sub_cancel,hza]
    exact haD
  · simpa only [Metric.mem_ball,dist_comm] using hp

lemma planar_positive_piece_frontier_zero {f : Plane → ℝ} (hf : Continuous f)
    {D C B : Set Plane} (hD : IsOpen D) (hC : IsClosed C)
    (hsub : D⊆{x | 0<f x}∩C)
    (hDC : ∀ x∈B,0<f x → x∈C → x∈D)
    {y : Plane} (hy : y∈frontier D) (hyB : y∈B) : f y=0 := by
  have hclC : closure D⊆C := closure_minimal (hsub.trans inter_subset_right) hC
  have hclP : closure D⊆{x | 0≤f x} := closure_minimal
    (fun x hx => show 0≤f x from (hsub hx).1.le) (isClosed_le continuous_const hf)
  have hyc := frontier_subset_closure hy
  have hnD : y∉D := by rw [hD.frontier_eq] at hy; exact hy.2
  exact le_antisymm (le_of_not_gt fun hp => hnD (hDC y hyB hp (hclC hyc))) (hclP hyc)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_NodalBalanceValue
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma HasDerivAt.eq_zero_of_right_zero {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0)
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ),f t=0) : d=0 := by
  have hp := deriv_nonneg_of_right_min hd (hf.mono fun t ht => by rw [h0,ht])
  have hn := deriv_nonneg_of_right_min hd.neg (hf.mono fun t ht => by
    simp only [Pi.neg_apply,h0,ht,neg_zero,le_refl])
  linarith

lemma HasDerivAt.neg_right_of_neg {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0) (hd0 : d<0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),f t<0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  filter_upwards [ht.eventually (eventually_lt_nhds hd0),self_mem_nhdsWithin] with t hs ht
  rw [slope_def_field,h0,sub_zero,sub_zero] at hs
  simpa only [zero_mul] using (div_lt_iff₀ ht).mp hs

lemma plane_hasDerivAt_line {F : Plane → ℝ} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (v : Plane) :
    HasDerivAt (fun t : ℝ => F (y+t • v)) (fderiv ℝ F y v) 0 := by
  have hh : HasFDerivAt F (fderiv ℝ F y) (y+id (0 : ℝ) • v) := by
    simpa only [id_eq,zero_smul,add_zero] using hF.hasFDerivAt
  simpa only [Function.comp_def,id_eq,one_smul] using
    hh.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add y)

theorem not_differentiable_nodal_splice
    {u F : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R k : ℝ} (hR : 0<R) (hk : k≠0)
    (hy : ‖y-c‖=R) (huy : u y=0)
    (hhopf : 0<fderiv ℝ u y (c-y))
    (hin : ∀ x,‖x-c‖<R → F x=k*u x)
    (hout : ∀ᶠ x in 𝓝 y,u x≤0 → F x=0) :
    ¬DifferentiableAt ℝ F y := by
  intro hF
  let v := c-y
  have hn (t : ℝ) : ‖y+t • v-c‖=|1-t| * R := by
    rw [show y+t • v-c=(1-t) • (y-c) by dsimp [v]; module,
      norm_smul,Real.norm_eq_abs,hy]
  have huin := plane_hasDerivAt_line (hu.differentiable (by simp) y) v
  have hFin := plane_hasDerivAt_line hF v
  have hFy : F y=0 := (hout.self_of_nhds) huy.le
  have hi : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • v)-k*u (y+t • v)=0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    have ht0 : 0<t := ht
    rw [hin,sub_self]
    rw [hn,abs_of_pos (sub_pos.mpr ht1)]
    nlinarith
  have hid := HasDerivAt.eq_zero_of_right_zero (hFin.sub (huin.const_mul k)) (by
    simp only [Pi.sub_apply,zero_smul,add_zero,hFy,huy,mul_zero,sub_self]) hi
  have huout : HasDerivAt (fun t : ℝ => u (y+t • (-v))) (-fderiv ℝ u y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line (hu.differentiable (by simp) y) (-v)
  have hFout : HasDerivAt (fun t : ℝ => F (y+t • (-v))) (-fderiv ℝ F y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line hF (-v)
  have ho := HasDerivAt.neg_right_of_neg huout (by simp [huy]) (neg_neg_of_pos hhopf)
  have ht : Tendsto (fun t : ℝ => y+t • (-v)) (𝓝 0) (𝓝 y) := by
    convert (show Continuous (fun t : ℝ => y+t • (-v)) from
      continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hfo : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • (-v))=0 := by
    filter_upwards [ho,(ht.eventually hout).filter_mono nhdsWithin_le_nhds] with t ht hf
    exact hf ht.le
  have hod := HasDerivAt.eq_zero_of_right_zero hFout (by simp [hFy]) hfo
  have hm : k*fderiv ℝ u y v=0 := by linarith
  exact (mul_ne_zero hk (ne_of_gt hhopf)) hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.no_nodal_splice_frontier
    {g u F : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {D : Set Plane} (hD : IsOpen D)
    {a : Plane} {ε k : ℝ} (hε : 0<ε) (hk : k≠0)
    (hp : ∀ x∈Metric.ball a ε,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball a ε))
    (hpos : ∀ x∈D∩Metric.ball a ε,0<u x)
    (hz : ∀ x∈frontier D∩Metric.ball a ε,u x=0)
    (hin : ∀ x∈D∩Metric.ball a ε,F x=k*u x)
    (hout : ∀ x∈Metric.ball a ε,u x≤0 → F x=0)
    (hF : DifferentiableOn ℝ F (Metric.ball a ε)) : a∉frontier D := by
  intro ha
  obtain ⟨c,y,R,hR,hball,hy,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
  have hb : Metric.ball c R⊆Metric.ball a ε := Metric.ball_subset_closedBall.trans hsub
  have hyb : y∈Metric.ball a ε := hsub (by
    simpa only [Metric.mem_closedBall,dist_eq_norm,hy] using (le_refl R))
  have huy := hz y ⟨hyD,hyb⟩
  have hh := (hw.mono hb).hopf hg hu hR (fun x hx => hp x (hsub hx))
    (fun x hx => hpos x ⟨hball hx,hb hx⟩) hy huy
  apply not_differentiable_nodal_splice hu hR hk hy huy hh ?_ ?_
    (hF.differentiableAt (Metric.isOpen_ball.mem_nhds hyb))
  · intro x hx
    have hx' : x∈Metric.ball c R := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    exact hin x ⟨hball hx',hb hx'⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyb] with x hx
    exact hout x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nodal_splice_closed_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (v : Cover) {D : Set Torus}
    (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*⟪v,N (representative a)⟫)
    (hFzero : ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫≤0 → F a=0) :
    IsClosed D := by
  let S := frontier (openRepresentative E)
  let t := directionalNormalScalar N hN hp v
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hDS : D⊆S := by
    intro a ha; rw [hDU] at ha; exact ha.1.1
  apply isClosed_of_closure_subset
  intro a ha
  by_contra haD
  have haS : a∈S := closure_minimal hDS isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hG0 : G 0=0 := by
    simp only [G,normalGraph,hg0,zero_smul,add_zero]
    exact (normalPlaneLinearIsometry n).map_zero
  have hφ0 : φ 0=a := by simp only [φ,hG0,add_zero,hxa]
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hm
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε ≤ r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  let W : Plane → ℝ := fun y => cmcWeight (gradient g y)
  let B : Plane → ℝ := fun y => W y*F (φ y)
  have hW (y : Plane) : 0<W y := cmcWeight_pos _
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=W y*⟪v,N (representative (φ y))⟫ := by
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _]
    rw [(hb y hy).1]
    exact normalTranslationNumerator_weight hn g v σ y
  have ht (b : Torus) : t.val (representative b)=⟪v,N (representative b)⟫ :=
    directionalNormalScalar_apply N hN hp v _
  let A : Set Plane := {y | 0<w y}∩φ ⁻¹' U∩Metric.ball 0 ε
  have hwo : ContDiff ℝ (⊤ : ℕ∞) w := normalTranslationNumerator_contDiff n hg v σ
  have hAo : IsOpen A := ((isOpen_lt continuous_const hwo.continuous).inter
    (hU.preimage hφ)).inter Metric.isOpen_ball
  have hAD (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) : y∈A ↔ φ y∈D := by
    rw [hDU]
    change (0<w y ∧ φ y∈U) ∧ y∈Metric.ball 0 ε ↔
      (φ y∈S ∧ 0<t.val (representative (φ y))) ∧ φ y∈U
    rw [ht,hws y hy,mul_pos_iff_of_pos_left (hW y)]
    exact ⟨fun h => ⟨⟨(hb y hy).2,h.1.1⟩,h.1.2⟩,
      fun h => ⟨⟨h.1.2,h.2⟩,hy⟩⟩
  have hAC (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      y∈A ↔ 0<w y ∧ φ y∈C := by
    rw [hAD y hy,hDC]
    change (φ y∈S ∧ 0<t.val (representative (φ y))) ∧ φ y∈C ↔ _
    rw [ht,hws y hy,mul_pos_iff_of_pos_left (hW y)]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨(hb y hy).2,h.1⟩,h.2⟩⟩
  have hAcl : (0 : Plane)∈closure A := by
    have hpc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hDS
      (hcover.mono fun z hz => hz.mp) (by rwa [hxa])
    rw [Metric.mem_closure_iff] at hpc ⊢
    intro δ hδ
    obtain ⟨y,hy,hyd⟩ := hpc (min δ ε) (lt_min hδ hε)
    have hye : y∈Metric.ball (0 : Plane) ε := by
      rw [Metric.mem_ball,dist_comm]
      exact hyd.trans_le (min_le_right _ _)
    exact ⟨y,(hAD y hye).mpr hy,hyd.trans_le (min_le_left _ _)⟩
  have hAf : (0 : Plane)∈frontier A := by
    rw [hAo.frontier_eq]
    refine ⟨hAcl,?_⟩
    intro hz
    have ha' := (hAD 0 (Metric.mem_ball_self hε)).mp hz
    rw [hφ0] at ha'
    exact haD ha'
  have hδ : 0<ε/2 := half_pos hε
  have hδs : Metric.ball (0 : Plane) (ε/2)⊆Metric.ball 0 ε :=
    Metric.ball_subset_ball (by linarith)
  have hB : DifferentiableOn ℝ B (Metric.ball (0 : Plane) (ε/2)) := by
    intro y hy
    have hnear : ∀ᶠ z in 𝓝 y,φ z∈S := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hδs hy)] with z hz
      exact (hb z hz).2
    have hf := isMinimizerAt_H1_jacobi_parametric_smooth hV hE hmin hμ
      N hN hp hae hNu hu hhom hFm hF hFu x (hG.contDiffAt (x := y)) hnear
    exact ((cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).contDiffAt.mul hf).differentiableAt
      (by simp) |>.differentiableWithinAt
  apply (normalTranslationNumerator_linear n hg v σ hlin |>.mono
    (hδs.trans (Metric.ball_subset_ball hεr))).no_nodal_splice_frontier
      hg hwo hAo hδ hk (fun y hy => hgrad y (Metric.ball_subset_ball hεr (hδs hy)))
      (fun y hy => hy.1.1.1) ?_ ?_ ?_ hB hAf
  · intro y hy
    apply planar_positive_piece_frontier_zero hwo.continuous hAo (hC.preimage hφ) ?_ ?_ hy.1 hy.2
    · intro z hz
      exact (hAC z hz.2).mp hz
    · intro z hz hw hc
      exact (hAC z (hδs hz)).mpr ⟨hw,hc⟩
  · intro y hy
    have hyε := hδs hy.2
    have hd := (hAD y hyε).mp hy.1
    change W y*F (φ y)=k*w y
    rw [hFD _ hd,hws y hyε]
    ring
  · intro y hy hwy
    have hyε := hδs hy
    have hnv : ⟪v,N (representative (φ y))⟫≤0 := by
      rw [hws y hyε] at hwy
      exact nonpos_of_mul_nonpos_right hwy (hW y)
    change W y*F (φ y)=0
    rw [hFzero _ (hb y hyε).2 hnv,mul_zero]

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_nodal_splice_closed_oai := @OAI.CubicTorus.isMinimizerAt_nodal_splice_closed_oai
