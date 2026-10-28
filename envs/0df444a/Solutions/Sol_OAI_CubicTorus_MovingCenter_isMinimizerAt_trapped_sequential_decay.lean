-- Prove2me | solution 1 for OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:49:53.249172+00:00
-- url     : https://prove2.me/submissions/36479e31-f068-4fe2-86b5-9091804a8db5

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_sequential_oriented_decay
import Theorems.Thm_OAI_CubicTorus_MovingCenter_weakCMC_normalized_sequence_harmonic
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_tightly_trapped_graph_approximation

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

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

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

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
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
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

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

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

end CubicTorus

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

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_UnitAngle
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval
namespace CubicTorus

lemma integral_square_le_mass {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x ↦ f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let m := μ.real univ
  let q := ∫ x, f x ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  by_cases hm0 : m = 0
  · have hμ0 : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (ENNReal.toReal_eq_zero_iff _).mp hm0 |>.resolve_right (measure_ne_top μ univ)
    simp [hμ0]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hi : Integrable (fun x ↦ f x ^ 2 - (2 * (q / m)) * f x) μ :=
    hfsq.sub (hf.const_mul _)
  have hp : 0 ≤ ∫ x, f x ^ 2 - (2 * (q / m)) * f x + (q / m) ^ 2 ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ f x ^ 2 - 2 * (q / m) * f x + (q / m) ^ 2
    nlinarith [sq_nonneg (f x - q / m)]
  rw [integral_add hi (integrable_const ((q / m) ^ 2)),
    integral_sub hfsq (hf.const_mul (2 * (q / m))), integral_const_mul, integral_const,
    smul_eq_mul] at hp
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 at hp
  have heq : (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 =
      (∫ x, f x ^ 2 ∂μ) - q ^ 2 / m := by field_simp; ring
  rw [heq] at hp
  exact (div_le_iff₀ hmpos).mp (by linarith : q ^ 2 / m ≤ ∫ x, f x ^ 2 ∂μ) |>.trans_eq (mul_comm _ _)

lemma lipschitz_deriv_sq_integrableOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    IntegrableOn (fun x ↦ deriv f x ^ 2) (Icc a b) := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
  · exact (aestronglyMeasurable_deriv f (volume.restrict (Icc a b))).pow 2
  · exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := norm_deriv_le_of_lipschitz hf (x₀ := x)
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (deriv f x), abs_nonneg (deriv f x), NNReal.coe_nonneg K]

lemma lipschitz_sq_sub_le_interval_energy {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hAC := hf.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hid : IntegrableOn (deriv f) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hAC.intervalIntegrable_deriv.1
  have hcs := integral_square_le_mass hid (lipschitz_deriv_sq_integrableOn hf a b)
  have hFTC : (∫ x in Icc a b, deriv f x) = f b - f a := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hab]
    exact hAC.integral_deriv_eq_sub
  simpa only [hFTC, Measure.restrict_apply_univ, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hcs

lemma integrable_square_sub_const {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (c : ℝ) :
    Integrable (fun x ↦ (c - f x) ^ 2) μ := by
  have h : (fun x ↦ (c - f x) ^ 2) =
      (fun x ↦ c ^ 2 - (2 * c) * f x + f x ^ 2) := by funext x; ring
  rw [h]
  exact ((integrable_const _).sub (hf.const_mul _)).add hfsq

lemma square_sub_average_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hm : 0 < μ.real univ) (hf : Integrable f μ)
    (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (c : ℝ) :
    (c - (∫ x, f x ∂μ) / μ.real univ) ^ 2 ≤
      (∫ x, (c - f x) ^ 2 ∂μ) / μ.real univ := by
  have hcs := integral_square_le_mass hf hfsq
  have hi : Integrable (fun x ↦ c ^ 2 - (2 * c) * f x) μ :=
    (integrable_const _).sub (hf.const_mul _)
  have he : (∫ x, (c - f x) ^ 2 ∂μ) =
      μ.real univ * c ^ 2 - (2 * c) * (∫ x, f x ∂μ) + ∫ x, f x ^ 2 ∂μ := by
    calc
      _ = ∫ x, c ^ 2 - (2 * c) * f x + f x ^ 2 ∂μ := integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      _ = _ := by
        rw [integral_add hi hfsq, integral_sub (integrable_const (c ^ 2)) (hf.const_mul (2 * c)),
          integral_const, integral_const_mul, smul_eq_mul]
  rw [he]
  have halg : (μ.real univ * c ^ 2 - (2 * c) * (∫ x, f x ∂μ) + ∫ x, f x ^ 2 ∂μ) /
      μ.real univ - (c - (∫ x, f x ∂μ) / μ.real univ) ^ 2 =
      (μ.real univ * (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2) / (μ.real univ) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (μ.real univ * (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2) /
      (μ.real univ) ^ 2 := div_nonneg (sub_nonneg.mpr hcs) (sq_nonneg _)
  linarith

lemma lipschitz_sq_sub_le_common_interval_energy {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    (f u - f v) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hab : a ≤ b := hu.1.trans hu.2
  have he (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      (f v - f u) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
    apply (lipschitz_sq_sub_le_interval_energy hf huv).trans
    apply mul_le_mul (by linarith [hu.1, hv.2] : v - u ≤ b - a)
      (setIntegral_mono_set (lipschitz_deriv_sq_integrableOn hf a b)
        (ae_of_all _ fun x ↦ sq_nonneg (deriv f x)) (ae_of_all _ fun _ hx ↦ Icc_subset_Icc hu.1 hv.2 hx))
      (integral_nonneg fun x ↦ sq_nonneg _) (sub_nonneg.mpr hab)
  rcases le_total u v with huv | hvu
  · simpa only [show (f v - f u) ^ 2 = (f u - f v) ^ 2 by ring] using he u v hu hv huv
  · exact he v u hv hu hvu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma variance_le_separated_pairwise {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f A B : X → ℝ}
    (hm : 0 < μ.real univ) (hf : Integrable f μ)
    (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (hA : Integrable A μ) (hB : Integrable B μ)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (f x - f y) ^ 2 ≤ A x + B y) :
    (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) ≤
      (∫ x, A x ∂μ) + ∫ y, B y ∂μ := by
  let m := (∫ y, f y ∂μ) / μ.real univ
  have hpoint : ∀ᵐ x ∂μ, (f x - m) ^ 2 ≤ A x + (∫ y, B y ∂μ) / μ.real univ := by
    filter_upwards [hpair] with x hx
    have hj := square_sub_average_le hm hf hfsq (f x)
    apply hj.trans
    apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ ∫ y, A x + B y ∂μ :=
        integral_mono_ae (integrable_square_sub_const hf hfsq _) ((integrable_const _).add hB) hx
      _ = (A x + (∫ y, B y ∂μ) / μ.real univ) * μ.real univ := by
        rw [integral_add (integrable_const _) hB, integral_const, smul_eq_mul]
        field_simp
  have hisq : Integrable (fun x ↦ (f x - m) ^ 2) μ := by
    convert integrable_square_sub_const hf hfsq m using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    ring
  have hh := integral_mono_ae hisq
    (hA.add (integrable_const ((∫ y, B y ∂μ) / μ.real univ))) hpoint
  change (∫ x, (f x - m) ^ 2 ∂μ) ≤ ∫ x, A x + (∫ y, B y ∂μ) / μ.real univ ∂μ at hh
  rw [integral_add hA (integrable_const _), integral_const, smul_eq_mul,
    mul_div_cancel₀ _ (ne_of_gt hm)] at hh
  exact hh

lemma lipschitz_product_partial_measurable {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Measurable (fun p : ℝ × ℝ ↦ deriv (fun x ↦ f (x, p.2)) p.1) ∧
      Measurable (fun p : ℝ × ℝ ↦ deriv (fun y ↦ f (p.1, y)) p.2) := by
  constructor
  · exact (measurable_deriv_with_param (f := fun y x ↦ f (x, y))
      (hf.continuous.comp continuous_swap)).comp measurable_swap
  · exact measurable_deriv_with_param (f := fun x y ↦ f (x, y)) hf.continuous

lemma lipschitz_product_partial_integrable {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ deriv (fun x ↦ f (x, p.2)) p.1 ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) ∧
    Integrable (fun p : ℝ × ℝ ↦ deriv (fun y ↦ f (p.1, y)) p.2 ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
  have hm := lipschitz_product_partial_measurable hf
  constructor
  · apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.1.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p ↦ by
      have hl : LipschitzWith K (fun x ↦ f (x, p.2)) := by simpa only [Function.comp_def, mul_one] using hf.comp (LipschitzWith.prodMk_right p.2)
      have hb := norm_deriv_le_of_lipschitz hl (x₀ := p.1)
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (deriv (fun x ↦ f (x, p.2)) p.1), NNReal.coe_nonneg K, abs_nonneg (deriv (fun x ↦ f (x, p.2)) p.1)]
  · apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.2.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p ↦ by
      have hl : LipschitzWith K (fun y ↦ f (p.1, y)) := by simpa only [Function.comp_def, mul_one] using hf.comp (LipschitzWith.prodMk_left p.1)
      have hb := norm_deriv_le_of_lipschitz hl (x₀ := p.2)
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (deriv (fun y ↦ f (p.1, y)) p.2), NNReal.coe_nonneg K, abs_nonneg (deriv (fun y ↦ f (p.1, y)) p.2)]

theorem lipschitz_box_poincare {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a < b) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
    (∫ p, (f p - (∫ q, f q ∂μ) / (b - a) ^ 2) ^ 2 ∂μ) ≤
      2 * (b - a) ^ 2 *
        ((∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 ∂μ) +
          ∫ p, deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ) := by
  dsimp only
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let μ := ν.prod ν
  let Ex : ℝ → ℝ := fun y ↦ ∫ x, deriv (fun t ↦ f (t, y)) x ^ 2 ∂ν
  let Ey : ℝ → ℝ := fun x ↦ ∫ y, deriv (fun t ↦ f (x, t)) y ^ 2 ∂ν
  have hν : ν.real univ = b - a := by simp [ν, measureReal_def, Real.volume_Icc, hab.le]
  have hμ : μ.real univ = (b - a) ^ 2 := by
    change ((ν.prod ν) univ).toReal = _
    rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    change ν.real univ * ν.real univ = _
    rw [hν]
    ring
  have hi : Integrable f μ := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuous.continuousOn
  have hisq : Integrable (fun p ↦ f p ^ 2) μ := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (hf.continuous.pow 2).continuousOn
  have hip := lipschitz_product_partial_integrable hf a b
  have hiEx : Integrable Ex ν := hip.1.integral_prod_right
  have hiEy : Integrable Ey ν := hip.2.integral_prod_left
  have hmem : ∀ᵐ p ∂μ, p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hpair : ∀ᵐ p ∂μ, ∀ᵐ q ∂μ,
      (f p - f q) ^ 2 ≤ 2 * (b - a) * Ex p.2 + 2 * (b - a) * Ey q.1 := by
    filter_upwards [hmem] with p hp
    filter_upwards [hmem] with q hq
    have hx : (f p - f (q.1, p.2)) ^ 2 ≤ (b - a) * Ex p.2 :=
      lipschitz_sq_sub_le_common_interval_energy (by
        simpa using hf.comp (LipschitzWith.prodMk_right p.2)) hp.1 hq.1
    have hy : (f (q.1, p.2) - f q) ^ 2 ≤ (b - a) * Ey q.1 :=
      lipschitz_sq_sub_le_common_interval_energy (by
        simpa using hf.comp (LipschitzWith.prodMk_left q.1)) hp.2 hq.2
    nlinarith [sq_nonneg (f p - 2 * f (q.1, p.2) + f q)]
  have hh := variance_le_separated_pairwise (μ := μ) (by rw [hμ]; positivity) hi hisq
    ((hiEx.comp_snd ν).const_mul (2 * (b - a)))
    ((hiEy.comp_fst ν).const_mul (2 * (b - a))) hpair
  rw [hμ] at hh
  have hex : (∫ p, Ex p.2 ∂μ) = (b - a) * ∫ y, Ex y ∂ν := by
    rw [integral_prod _ (hiEx.comp_snd ν)]
    simp only [integral_const, smul_eq_mul, hν]
  have hey : (∫ p, Ey p.1 ∂μ) = (b - a) * ∫ x, Ey x ∂ν := by
    rw [integral_prod _ (hiEy.comp_fst ν)]
    simp only [integral_const, smul_eq_mul, hν, integral_const_mul]
  have hEx : (∫ y, Ex y ∂ν) = ∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 ∂μ :=
    (integral_prod_symm _ hip.1).symm
  have hEy : (∫ x, Ey x ∂ν) = ∫ p, deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ :=
    (integral_prod _ hip.2).symm
  rw [integral_const_mul, integral_const_mul, hex, hey, hEx, hEy] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma differentiableAt_partial_sq_le {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 + deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ≤
      2 * ‖fderiv ℝ f p‖ ^ 2 := by
  have hx : deriv (fun x ↦ f (x, p.2)) p.1 = fderiv ℝ f p (1, 0) := by
    exact (hf.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  have hy : deriv (fun y ↦ f (p.1, y)) p.2 = fderiv ℝ f p (0, 1) := by
    exact (hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  rw [hx, hy]
  have hb₁ : |fderiv ℝ f p (1, 0)| ≤ ‖fderiv ℝ f p‖ := by
    simpa [Prod.norm_def] using (fderiv ℝ f p).le_opNorm (1, 0)
  have hb₂ : |fderiv ℝ f p (0, 1)| ≤ ‖fderiv ℝ f p‖ := by
    simpa [Prod.norm_def] using (fderiv ℝ f p).le_opNorm (0, 1)
  nlinarith [sq_abs (fderiv ℝ f p (1, 0)), sq_abs (fderiv ℝ f p (0, 1)),
    abs_nonneg (fderiv ℝ f p (1, 0)), abs_nonneg (fderiv ℝ f p (0, 1))]

lemma lipschitz_fderiv_sq_integrable {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
    nlinarith [norm_nonneg (fderiv ℝ f x), NNReal.coe_nonneg K]

theorem lipschitz_box_poincare_fderiv {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a < b) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
    (∫ p, (f p - (∫ q, f q ∂μ) / (b - a) ^ 2) ^ 2 ∂μ) ≤
      4 * (b - a) ^ 2 * (∫ p, ‖fderiv ℝ f p‖ ^ 2 ∂μ) := by
  dsimp only
  let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
  have hdiff : ∀ᵐ p ∂μ, DifferentiableAt ℝ f p := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ae_restrict_of_ae hf.ae_differentiableAt
  have hip := lipschitz_product_partial_integrable hf a b
  have hb := integral_mono_ae (hip.1.add hip.2)
    ((lipschitz_fderiv_sq_integrable (μ := μ) hf).const_mul 2)
    (hdiff.mono fun _ h ↦ differentiableAt_partial_sq_le h)
  change (∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 +
    deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ) ≤ ∫ p, 2 * ‖fderiv ℝ f p‖ ^ 2 ∂μ at hb
  rw [integral_add hip.1 hip.2, integral_const_mul] at hb
  apply (lipschitz_box_poincare hf hab).trans
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * (b - a) ^ 2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallProbability
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
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

lemma lipschitz_affine_line {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a h : X) : LipschitzWith ‖h‖₊ (fun t : ℝ ↦ a + t • h) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs,
    Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

theorem lipschitz_translation_square_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    (h : X) :
    Integrable (fun x ↦ (f (x + h) - f x) ^ 2) μ ∧
      (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
        ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  let G : X × ℝ → ℝ := fun p ↦ ‖fderiv ℝ f (p.1 + p.2 • h)‖ ^ 2
  have hν : ν.real univ = 1 := by norm_num [ν, measureReal_def, Real.volume_Icc]
  have hflow : Continuous (fun p : X × ℝ ↦ p.1 + p.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hG : Measurable G := ((measurable_fderiv ℝ f).comp hflow.measurable).norm.pow_const 2
  have hmd : MeasurableSet {p : X × ℝ | DifferentiableAt ℝ f (p.1 + p.2 • h)} :=
    (measurableSet_of_differentiableAt ℝ f).preimage hflow.measurable
  have hdiff : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, DifferentiableAt ℝ f (x + t • h) := by
    apply (Measure.ae_ae_comm hmd).mpr
    exact ae_of_all _ fun t ↦ (measurePreserving_add_right μ (t • h)).quasiMeasurePreserving.ae
      hf.ae_differentiableAt
  have htI (t : ℝ) : Integrable (fun x ↦ G (x, t)) μ :=
    (measurePreserving_add_right μ (t • h)).integrable_comp hgrad.aestronglyMeasurable |>.mpr hgrad
  have hswap : Integrable (fun p : ℝ × X ↦ G (p.2, p.1)) (ν.prod μ) := by
    apply (integrable_prod_iff (hG.comp measurable_swap).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ htI, ?_⟩
    have he : (fun t ↦ ∫ x, ‖G (x, t)‖ ∂μ) =
        (fun _ : ℝ ↦ ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) := by
      funext t
      dsimp only [G]
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact integral_add_right_eq_self (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (t • h)
    change Integrable (fun t ↦ ∫ x, ‖G (x, t)‖ ∂μ) ν
    rw [he]
    exact integrable_const _
  have hprod : Integrable G (μ.prod ν) := hswap.swap
  have hGI : Integrable (fun x ↦ ∫ t, G (x, t) ∂ν) μ := hprod.integral_prod_left
  have hpoint : ∀ᵐ x ∂μ, (f (x + h) - f x) ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t, G (x, t) ∂ν := by
    filter_upwards [hdiff, hprod.prod_right_ae] with x hx hi
    have hl : LipschitzWith (K * ‖h‖₊) (fun t : ℝ ↦ f (x + t • h)) :=
      hf.comp (lipschitz_affine_line x h)
    have hFTC := lipschitz_sq_sub_le_interval_energy hl (by norm_num : (0 : ℝ) ≤ 1)
    simp only [one_smul, zero_smul, add_zero, sub_zero, one_mul] at hFTC
    apply hFTC.trans
    have hc : ∀ᵐ t ∂ν, deriv (fun s : ℝ ↦ f (x + s • h)) t ^ 2 ≤
        ‖h‖ ^ 2 * G (x, t) := by
      filter_upwards [hx] with t ht
      have he : deriv (fun s : ℝ ↦ f (x + s • h)) t = fderiv ℝ f (x + t • h) h := by
        have hh := ht.hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).smul_const h |>.const_add x)
        simpa only [Function.comp_def, one_smul, id_eq] using hh.deriv
      rw [he]
      have hb := (fderiv ℝ f (x + t • h)).le_opNorm h
      rw [Real.norm_eq_abs] at hb
      dsimp [G]
      nlinarith [sq_abs (fderiv ℝ f (x + t • h) h),
        abs_nonneg (fderiv ℝ f (x + t • h) h),
        mul_nonneg (norm_nonneg (fderiv ℝ f (x + t • h))) (norm_nonneg h)]
    have hh := integral_mono_ae (lipschitz_deriv_sq_integrableOn hl 0 1)
      (hi.const_mul (‖h‖ ^ 2)) hc
    simpa only [integral_const_mul] using hh
  have hleft : Integrable (fun x ↦ (f (x + h) - f x) ^ 2) μ := by
    apply (hGI.const_mul (‖h‖ ^ 2)).mono'
      (((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).pow 2).aestronglyMeasurable
    filter_upwards [hpoint] with x hx
    change ‖(f (x + h) - f x) ^ 2‖ ≤ _
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hleft, (integral_mono_ae hleft (hGI.const_mul (‖h‖ ^ 2)) hpoint).trans_eq ?_⟩
  rw [integral_const_mul, integral_integral_swap hprod]
  have he : (∫ t, ∫ x, G (x, t) ∂μ ∂ν) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    have htint (t : ℝ) : (∫ x, G (x, t) ∂μ) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
      integral_add_right_eq_self (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (t • h)
    simp only [htint, integral_const, smul_eq_mul, hν, one_mul]
  rw [he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem lipschitz_average_translation_square_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) :
    Integrable (fun x ↦ (∫ y, f (x - y) - f x ∂ν) ^ 2) μ ∧
      (∫ x, (∫ y, f (x - y) - f x ∂ν) ^ 2 ∂μ) ≤
        δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let D : X × X → ℝ := fun p ↦ f (p.2 - p.1) - f p.2
  have hD : Continuous D :=
    (hf.continuous.comp (continuous_snd.sub continuous_fst)).sub
      (hf.continuous.comp continuous_snd)
  have hdpoint (x : X) : ∀ᵐ y ∂ν, |D (y, x)| ≤ (K : ℝ) * δ := by
    filter_upwards [hν] with y hy
    have hh := hf.dist_le_mul (x - y) x
    rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
  have hdi (x : X) : Integrable (fun y ↦ D (y, x)) ν := by
    apply (integrable_const ((K : ℝ) * δ)).mono'
      (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using hdpoint x
  have hdi₂ (x : X) : Integrable (fun y ↦ D (y, x) ^ 2) ν := by
    apply (integrable_const (((K : ℝ) * δ) ^ 2)).mono'
      ((hD.comp (continuous_id.prodMk continuous_const)).pow 2).aestronglyMeasurable
    filter_upwards [hdpoint x] with y hy
    change ‖D (y, x) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (D (y, x)), abs_nonneg (D (y, x)), mul_nonneg K.coe_nonneg hδ]
  have hJ (y : X) : Integrable (fun x ↦ D (y, x) ^ 2) μ ∧
      (∫ x, D (y, x) ^ 2 ∂μ) ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    simpa only [D, sub_eq_add_neg, norm_neg] using lipschitz_translation_square_le hf hgrad (-y)
  have hJe : ∀ᵐ y ∂ν, (∫ x, D (y, x) ^ 2 ∂μ) ≤
      δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    filter_upwards [hν] with y hy
    apply (hJ y).2.trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ ↦ sq_nonneg _))
    nlinarith [norm_nonneg y]
  have hprod : Integrable (fun p : X × X ↦ D p ^ 2) (ν.prod μ) := by
    apply (integrable_prod_iff (hD.pow 2).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun y ↦ (hJ y).1, ?_⟩
    have he (y : X) : (∫ x, ‖D (y, x) ^ 2‖ ∂μ) = ∫ x, D (y, x) ^ 2 ∂μ := by
      congr 1
      funext x
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun y ↦ ∫ x, ‖D (y, x) ^ 2‖ ∂μ) ν
    simp_rw [he]
    apply (integrable_const (δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)).mono'
      (hD.pow 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hJe] with y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
  have hA (x : X) : (∫ y, D (y, x) ∂ν) ^ 2 ≤ ∫ y, D (y, x) ^ 2 ∂ν := by
    have hh := integral_square_le_mass (hdi x) (hdi₂ x)
    simpa only [probReal_univ, one_mul] using hh
  have hAI : Integrable (fun x ↦ (∫ y, D (y, x) ∂ν) ^ 2) μ := by
    apply hprod.integral_prod_right.mono'
      (hD.stronglyMeasurable.integral_prod_left'.pow 2).aestronglyMeasurable
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hA x
  refine ⟨hAI, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, D (y, x) ^ 2 ∂ν ∂μ :=
      integral_mono hAI hprod.integral_prod_right hA
    _ = ∫ y, ∫ x, D (y, x) ^ 2 ∂μ ∂ν := integral_integral_swap hprod.swap
    _ ≤ ∫ _y, δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ ∂ν :=
      integral_mono_ae hprod.integral_prod_left (integrable_const _) hJe
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma probability_dominated_square {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsProbabilityMeasure ν] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hν : ν ≤ c • μ) {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ) :
    Integrable f ν ∧ Integrable (fun x ↦ f x ^ 2) ν ∧
      (∫ x, f x ∂ν) ^ 2 ≤ c.toReal * ∫ x, f x ^ 2 ∂μ := by
  have hi : Integrable (fun x ↦ f x ^ 2) ν := (hfs.smul_measure hc).mono_measure hν
  have hm : AEStronglyMeasurable f ν := (hf.smul_measure c).mono_measure hν
  have him : MemLp f 2 ν := (memLp_two_iff_integrable_sq hm).mpr hi
  have hif : Integrable f ν := him.integrable (by norm_num)
  refine ⟨hif, hi, ?_⟩
  have hj := integral_square_le_mass hif hi
  simp only [probReal_univ, one_mul] at hj
  apply hj.trans
  have hb := integral_mono_measure hν (ae_of_all _ fun x ↦ sq_nonneg (f x))
    (hfs.smul_measure hc)
  simpa only [integral_smul_measure, smul_eq_mul] using hb

theorem h1_average_bounds {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hν : ν ≤ c • μ)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {M D : ℝ} (hM : (∫ x, f x ^ 2 ∂μ) ≤ M)
    (hD : (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) ≤ D) :
    (∀ x, |∫ y, f (x - y) ∂ν| ≤ Real.sqrt (c.toReal * M)) ∧
      LipschitzWith ⟨Real.sqrt (c.toReal * D), Real.sqrt_nonneg _⟩
        (fun x ↦ ∫ y, f (x - y) ∂ν) := by
  have ht (x : X) : Integrable (fun y ↦ f (x - y) ^ 2) μ :=
    (μ.measurePreserving_sub_left x).integrable_comp hfs.aestronglyMeasurable |>.mpr hfs
  have hp (x : X) := probability_dominated_square (f := fun y ↦ f (x - y)) hc hν
    ((hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) (ht x)
  have hMnon : 0 ≤ M := (integral_nonneg (fun _ ↦ sq_nonneg _)).trans hM
  have hDnon : 0 ≤ D := (integral_nonneg (fun _ ↦ sq_nonneg _)).trans hD
  constructor
  · intro x
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg ENNReal.toReal_nonneg hMnon)).mpr
    rw [sq_abs]
    apply (hp x).2.2.trans
    rw [integral_sub_left_eq_self (fun y ↦ f y ^ 2) μ x]
    exact mul_le_mul_of_nonneg_left hM ENNReal.toReal_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x z
    have hj := lipschitz_translation_square_le hf hgrad (x - z)
    have hi : Integrable (fun y ↦ (f (x - y) - f (z - y)) ^ 2) μ := by
      have hh := (μ.measurePreserving_sub_left z).integrable_comp hj.1.aestronglyMeasurable |>.mpr hj.1
      have heq (y : X) : z - y + (x - z) = x - y := by abel
      simpa only [Function.comp_def, heq] using hh
    have hp' := probability_dominated_square (f := fun y ↦ f (x - y) - f (z - y)) hc hν
      (((hf.continuous.comp (continuous_const.sub continuous_id)).sub
        (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) hi
    have he : (∫ y, (f (x - y) - f (z - y)) ^ 2 ∂μ) =
        ∫ y, (f (y + (x - z)) - f y) ^ 2 ∂μ := by
      have hh := integral_sub_left_eq_self (fun y ↦ (f (y + (x - z)) - f y) ^ 2) μ z
      have heq (y : X) : z - y + (x - z) = x - y := by abel
      simpa only [heq] using hh
    rw [integral_sub (hp x).1 (hp z).1, he] at hp'
    have hb := hp'.2.2.trans (mul_le_mul_of_nonneg_left hj.2 ENNReal.toReal_nonneg)
    have hs := mul_le_mul_of_nonneg_left hD (mul_nonneg (show 0 ≤ c.toReal from ENNReal.toReal_nonneg) (sq_nonneg ‖x - z‖))
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν| ≤
      Real.sqrt (c.toReal * D) * ‖x - z‖
    have hr := Real.sq_sqrt (mul_nonneg (show 0 ≤ c.toReal from ENNReal.toReal_nonneg) hDnon)
    nlinarith [sq_abs ((∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν),
      abs_nonneg ((∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν),
      mul_nonneg (Real.sqrt_nonneg (c.toReal * D)) (norm_nonneg (x - z))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
lemma closedBall_haar_ne_zero {δ : ℝ} (hδ : 0 < δ) : μ (closedBall (0 : X) δ) ≠ 0 := by
  apply ne_of_gt
  exact (isOpen_ball.measure_pos μ (nonempty_ball.mpr hδ)).trans_le
    (measure_mono ball_subset_closedBall)

omit [BorelSpace X] in
lemma ballProbability_isProbability {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (ballProbability μ δ) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [ballProbability, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (closedBall_haar_ne_zero μ hδ)
    (isCompact_closedBall (0 : X) δ).measure_lt_top.ne

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] [μ.IsAddHaarMeasure] in
lemma ballProbability_domination (δ : ℝ) :
    ballProbability μ δ ≤ (μ (closedBall (0 : X) δ))⁻¹ • μ := by
  dsimp only [ballProbability]
  gcongr
  exact Measure.restrict_le_self

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [μ.IsAddHaarMeasure] in
lemma ballProbability_ae_norm_le (δ : ℝ) :
    ∀ᵐ y ∂ballProbability μ δ, ‖y‖ ≤ δ := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
  simpa only [mem_closedBall, dist_zero_right] using hy

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
lemma ballProbability_density_ne_top {δ : ℝ} (hδ : 0 < δ) :
    (μ (closedBall (0 : X) δ))⁻¹ ≠ ⊤ := by
  exact ENNReal.inv_ne_top.mpr (closedBall_haar_ne_zero μ hδ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma boundedContinuous_L2_dist_sq {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {η : Measure Y} [IsFiniteMeasure η]
    (f g : BoundedContinuousFunction Y ℝ) :
    dist ((BoundedContinuousFunction.toLp 2 η ℝ) f)
      ((BoundedContinuousFunction.toLp 2 η ℝ) g) ^ 2 = ∫ y, (f y - g y) ^ 2 ∂η := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub ((BoundedContinuousFunction.toLp 2 η ℝ) f)
    ((BoundedContinuousFunction.toLp 2 η ℝ) g),
    BoundedContinuousFunction.coeFn_toLp 2 η ℝ f,
    BoundedContinuousFunction.coeFn_toLp 2 η ℝ g] with y hy hf hg
  rw [hy]
  change (((BoundedContinuousFunction.toLp 2 η ℝ) f) y -
    ((BoundedContinuousFunction.toLp 2 η ℝ) g) y) *
    (((BoundedContinuousFunction.toLp 2 η ℝ) f) y -
    ((BoundedContinuousFunction.toLp 2 η ℝ) g) y) = _
  rw [hf, hg, pow_two]

lemma h1_average_error {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hν : ν ≤ c • μ)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδν : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) :
    Integrable (fun x ↦ ((∫ y, f (x - y) ∂ν) - f x) ^ 2) μ ∧
      (∫ x, ((∫ y, f (x - y) ∂ν) - f x) ^ 2 ∂μ) ≤
        δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  have hi (x : X) : Integrable (fun y ↦ f (x - y)) ν := by
    have ht : Integrable (fun y ↦ f (x - y) ^ 2) μ :=
      (μ.measurePreserving_sub_left x).integrable_comp hfs.aestronglyMeasurable |>.mpr hfs
    exact (probability_dominated_square (f := fun y ↦ f (x - y)) hc hν
      (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ht).1
  have he (x : X) : (∫ y, f (x - y) - f x ∂ν) = (∫ y, f (x - y) ∂ν) - f x := by
    rw [integral_sub (hi x) (integrable_const _), integral_const, probReal_univ, one_smul]
  simpa only [he] using lipschitz_average_translation_square_le hf hgrad hδ hδν

theorem totallyBounded_local_H1 {X Y ι : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {η : Measure Y} [IsFiniteMeasure η] {e : Y → X} (he : LipschitzWith 1 e)
    (hmap : Measure.map e η ≤ μ) (f : ι → X → ℝ) (K : ι → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    TotallyBounded (range (fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
      (BoundedContinuousFunction.mkOfCompact
        ⟨fun y ↦ f i (e y), (hf i).continuous.comp he.continuous⟩))) := by
  let F : ι → BoundedContinuousFunction Y ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦ f i (e y), (hf i).continuous.comp he.continuous⟩
  let T : (BoundedContinuousFunction Y ℝ) →L[ℝ] Lp ℝ 2 η :=
    BoundedContinuousFunction.toLp 2 η ℝ
  change TotallyBounded (range (fun i ↦ T (F i)))
  rw [Metric.totallyBounded_iff]
  intro ε hε
  let δ := ε / (2 * (Real.sqrt D + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let ν := ballProbability μ δ
  let c := (μ (Metric.closedBall (0 : X) δ))⁻¹
  let : IsProbabilityMeasure ν := ballProbability_isProbability μ hδ
  have hc : c ≠ ⊤ := ballProbability_density_ne_top μ hδ
  have hν : ν ≤ c • μ := ballProbability_domination μ δ
  let L : ℝ≥0 := ⟨Real.sqrt (c.toReal * D), Real.sqrt_nonneg _⟩
  have hb (i) := h1_average_bounds hc hν (hf i) (hfs i) (hgrad i) (hM i) (hD i)
  let G : ι → BoundedContinuousFunction Y ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ ∫ y, f i (e x - y) ∂ν, (hb i).2.continuous.comp he.continuous⟩
  have hl (i) : LipschitzWith L (G i) := by
    change LipschitzWith L ((fun x ↦ ∫ y, f i (x - y) ∂ν) ∘ e)
    convert (hb i).2.comp he using 1
    all_goals try with_reducible_and_instances rfl
    exact (mul_one L).symm
  have hEq : Equicontinuous ((↑) : range G → Y → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    rintro ⟨_, i, rfl⟩
    exact hl i
  have hbounded (g : BoundedContinuousFunction Y ℝ) (x : Y) (hg : g ∈ range G) :
      g x ∈ Icc (-Real.sqrt (c.toReal * M)) (Real.sqrt (c.toReal * M)) := by
    obtain ⟨i, rfl⟩ := hg
    exact abs_le.mp ((hb i).1 (e x))
  have hcompact := BoundedContinuousFunction.arzela_ascoli
    (Icc (-Real.sqrt (c.toReal * M)) (Real.sqrt (c.toReal * M))) isCompact_Icc
    (range G) hbounded hEq
  have htb : TotallyBounded (range (fun i ↦ T (G i))) := by
    apply (hcompact.image T.continuous).totallyBounded.subset
    rintro _ ⟨i, rfl⟩
    exact ⟨G i, subset_closure (mem_range_self i), rfl⟩
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (half_pos hε)
  refine ⟨s, hs, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨z, hz, hiz⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  have herr := h1_average_error hc hν (hf i) (hfs i) (hgrad i) hδ.le
    (ballProbability_ae_norm_le μ δ)
  have hlocal : (∫ y, ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2 ∂η) ≤
      δ ^ 2 * D := by
    have hi := herr.1.mono_measure hmap
    rw [← integral_map he.continuous.measurable.aemeasurable hi.aestronglyMeasurable]
    exact (integral_mono_measure hmap (ae_of_all _ fun _ ↦ sq_nonneg _) herr.1).trans
      (herr.2.trans (mul_le_mul_of_nonneg_left (hD i) (sq_nonneg δ)))
  have hdist : dist (T (F i)) (T (G i)) ≤ δ * Real.sqrt D := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg hδ.le (Real.sqrt_nonneg _))).mp
    rw [boundedContinuous_L2_dist_sq, mul_pow, Real.sq_sqrt hDnon]
    calc
      (∫ y, ((F i) y - (G i) y) ^ 2 ∂η) =
          (∫ y, ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2 ∂η) := by
        apply integral_congr_ae
        filter_upwards [] with y
        change (f i (e y) - (∫ z, f i (e y - z) ∂ν)) ^ 2 =
          ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2
        ring
      _ ≤ δ ^ 2 * D := hlocal
  have hsmall : δ * Real.sqrt D < ε / 2 := by
    have hden : 0 < 2 * (Real.sqrt D + 1) := by positivity
    have heq : δ * (2 * (Real.sqrt D + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  have hiz' : dist (T (G i)) z < ε / 2 := hiz
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem local_H1_subsequence {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {η : Measure Y} [IsFiniteMeasure η] {e : Y → X} (he : LipschitzWith 1 e)
    (hmap : Measure.map e η ≤ μ) (f : ℕ → X → ℝ) (K : ℕ → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    ∃ g : Lp ℝ 2 η, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun y ↦ f (φ i) (e y), (hf (φ i)).continuous.comp he.continuous⟩))
        atTop (𝓝 g) := by
  have ht := totallyBounded_local_H1 he hmap f K hf hfs hgrad hDnon hM hD
  obtain ⟨g, _, φ, hφ, hg⟩ := (ht.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun i ↦ subset_closure (mem_range_self i))
  exact ⟨g, φ, hφ, hg⟩

lemma L2_pairing_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hg : Tendsto g atTop (𝓝 u))
    (v : Lp ℝ 2 μ) :
    Tendsto (fun i ↦ ∫ x, g i x * v x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  have hh := hg.inner tendsto_const_nhds (𝕜 := ℝ) (g := fun _ : ℕ ↦ v)
  simpa only [L2.inner_def, RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using hh

lemma L2_pairing_limit_zero {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hg : Tendsto g atTop (𝓝 u))
    (v : Lp ℝ 2 μ)
    (hz : Tendsto (fun i ↦ ∫ x, g i x * v x ∂μ) atTop (𝓝 0)) :
    (∫ x, u x * v x ∂μ) = 0 :=
  tendsto_nhds_unique (L2_pairing_tendsto hg v) hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem restricted_H1_subsequence {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {K : Set X} (hK : IsCompact K)
    (f : ℕ → X → ℝ) (L : ℕ → ℝ≥0) (hf : ∀ i, LipschitzWith (L i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    ∃ (u : Lp ℝ 2 (μ.restrict K)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ hmem : ∀ i, MemLp (f i) 2 (μ.restrict K),
        Tendsto (fun i ↦ (hmem (φ i)).toLp (f (φ i))) atTop (𝓝 u) := by
  let η : Measure K := Measure.comap Subtype.val μ
  have hv := measurePreserving_subtype_coe (μa := μ) hK.measurableSet
  change MeasurePreserving ((↑) : K → X) η (μ.restrict K) at hv
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (Measure.map ((↑) : K → X) η) := hv.map_eq.symm ▸ inferInstance
  let : IsFiniteMeasure η := Measure.isFiniteMeasure_of_map hv.measurable.aemeasurable
  obtain ⟨g, φ, hφ, hg⟩ := local_H1_subsequence (μ := μ) (η := η)
    (isometry_subtype_coe.lipschitz : LipschitzWith 1 ((↑) : K → X))
    (by rw [hv.map_eq]; exact Measure.restrict_le_self)
    f L hf hfs hgrad hDnon hM hD
  have hmem (i : ℕ) : MemLp (f i) 2 (μ.restrict K) :=
    (MemLp.mono_measure Measure.restrict_le_self)
      ((memLp_two_iff_integrable_sq (hf i).continuous.aestronglyMeasurable).mpr (hfs i))
  let F : ℕ → Lp ℝ 2 (μ.restrict K) := fun i ↦ (hmem i).toLp (f i)
  let G : ℕ → Lp ℝ 2 η := fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun y : K ↦ f i y, (hf i).continuous.comp continuous_subtype_val⟩)
  let T := Lp.compMeasurePreserving ((↑) : K → X) hv (E := ℝ) (p := 2)
  have he (i : ℕ) : T (F i) = G i := by
    apply Lp.ext
    have hi := (hmem i).coeFn_toLp
    have hi' : ∀ᵐ (x : K) ∂η, F i (x : X) = f i (x : X) := by
      apply ae_of_ae_map (μ := η) (p := fun x : X ↦ F i x = f i x)
        hv.measurable.aemeasurable
      rw [hv.map_eq]
      exact hi
    filter_upwards [Lp.coeFn_compMeasurePreserving (F i) hv, hi',
      BoundedContinuousFunction.coeFn_toLp 2 η ℝ
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun y : K ↦ f i y, (hf i).continuous.comp continuous_subtype_val⟩)] with x hx hi hxG
    exact hx.trans (hi.trans hxG.symm)
  have hdist (i j : ℕ) : dist (F i) (F j) = dist (G i) (G j) := by
    rw [← he i, ← he j]
    exact ((Lp.isometry_compMeasurePreserving hv).dist_eq _ _).symm
  have hc : CauchySeq (fun i ↦ F (φ i)) := by
    have hg' : Tendsto (fun i ↦ G (φ i)) atTop (𝓝 g) := hg
    have hcg := Metric.cauchySeq_iff.mp hg'.cauchySeq
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hcg ε hε
    exact ⟨N, fun m hm n hn ↦ by rw [hdist]; exact hN m hm n hn⟩
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨u, φ, hφ, hmem, hu⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVTangentialBlowup
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

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

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

lemma image_quotientMap_eq_preimage_representative {S : Set Cover}
    (hS : S ⊆ fundamentalCube) : quotientMap '' S = representative ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change representative (quotientMap v) ∈ S
    rwa [representative_quotientMap_of_mem (hS hv)]
  · intro hx
    exact ⟨representative x, hx, quotientMap_representative x⟩

lemma torusVolume_quotientMap_image_cube {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ fundamentalCube) : torusVolume (quotientMap '' S) = volume S := by
  have hi : MeasurableSet (quotientMap '' S) := by
    rw [image_quotientMap_eq_preimage_representative hc]
    exact hS.preimage measurable_representative
  rw [torusVolume, Measure.map_apply measurable_quotientMap hi,
    Measure.restrict_apply (hi.preimage measurable_quotientMap)]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hc'⟩
    rw [image_quotientMap_eq_preimage_representative hc] at hx
    change representative (quotientMap x) ∈ S at hx
    rwa [representative_quotientMap_of_mem hc'] at hx
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hc hx⟩

lemma haar_image_add_right {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddRightInvariant] (a : G) (S : Set G) :
    μ ((fun x ↦ x + a) '' S) = μ S := by
  have he : (fun x ↦ x + a) '' S = (fun x ↦ x + (-a)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + (-a), hx, by simp⟩
  rw [he, measure_preimage_add_right]

lemma measurableSet_image_add_right {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (a : G) {S : Set G} (hS : MeasurableSet S) :
    MeasurableSet ((fun x ↦ x + a) '' S) := by
  have he : (fun x ↦ x + a) '' S = (fun x ↦ x + (-a)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + (-a), hx, by simp⟩
  rw [he]
  exact hS.preimage (measurable_id.add_const _)

lemma torusVolume_quotientMap_image_local {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ Metric.ball (0 : Cover) (1 / 2)) :
    torusVolume (quotientMap '' S) = volume S := by
  let T := (fun x : Cover ↦ x + cubeCenter) '' S
  have hT : MeasurableSet T := measurableSet_image_add_right _ hS
  have hTc : T ⊆ fundamentalCube := by
    rintro x ⟨v, hv, rfl⟩
    apply coverBall_subset_cube (le_refl (1 / 2 : ℝ))
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hc hv
  have he : quotientMap '' T = (fun x : Torus ↦ x + quotientMap cubeCenter) '' (quotientMap '' S) := by
    simp only [T, image_image, quotientMap_add]
  have hh := torusVolume_quotientMap_image_cube hT hTc
  rw [he, haar_image_add_right] at hh
  exact hh.trans (haar_image_add_right volume cubeCenter S)

lemma torusVolume_chart_image {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ Metric.ball (0 : Cover) (1 / 2)) (c : Torus) :
    torusVolume ((fun v ↦ quotientMap v + c) '' S) = volume S := by
  rw [show (fun v ↦ quotientMap v + c) '' S =
    (fun x : Torus ↦ x + c) '' (quotientMap '' S) by rw [image_image],
    haar_image_add_right]
  exact torusVolume_quotientMap_image_local hS hc

lemma quotientMap_chart_image_ball (c : Torus) {r : ℝ} (hr : r ≤ 1 / 2) :
    (fun v ↦ quotientMap v + c) '' Metric.ball (0 : Cover) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change dist (quotientMap v + c) c < r
    rw [dist_eq_norm, add_sub_cancel_right, ← norm_shortestLift,
      shortestLift_quotientMap ((show ‖v‖ < r by simpa using hv).trans_le hr)]
    simpa using hv
  · intro hx
    refine ⟨shortestLift (x - c), ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_shortestLift, ← dist_eq_norm] using hx
    · simp only [quotientMap_shortestLift, sub_add_cancel]

lemma torusVolume_chart_map_restrict (c : Torus) {r : ℝ} (hr : r ≤ 1 / 2) :
    Measure.map (fun v ↦ quotientMap v + c) (volume.restrict (Metric.ball (0 : Cover) r)) =
      torusVolume.restrict (Metric.ball c r) := by
  have hm : Measurable (fun v ↦ quotientMap v + c) := measurable_quotientMap.add_const c
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hA.preimage hm), Measure.restrict_apply hA]
  rw [← torusVolume_chart_image ((hA.preimage hm).inter Metric.isOpen_ball.measurableSet)
    (fun _ hx ↦ Metric.ball_subset_ball hr hx.2) c]
  congr 1
  rw [inter_comm ((fun v ↦ quotientMap v + c) ⁻¹' A), Set.image_inter_preimage,
    quotientMap_chart_image_ball c hr, inter_comm]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
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

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

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

lemma plane_ball_real {s : ℝ} (hs : 0 ≤ s) :
    (volume : Measure Plane).real (Metric.ball 0 s) = Real.pi * s ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

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

lemma laplacian_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ (f ∘ L) x = Δ f (L x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ L)
    (stdOrthonormalBasis ℝ X),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((stdOrthonormalBasis ℝ X).map L)]
  apply Finset.sum_congr rfl
  intro i _
  have hh := L.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hh' := congrArg (fun A ↦ A ![(stdOrthonormalBasis ℝ X) i,
    (stdOrthonormalBasis ℝ X) i]) hh
  have hv : (fun j : Fin 2 ↦ L (![ (stdOrthonormalBasis ℝ X) i,
      (stdOrthonormalBasis ℝ X) i] j)) =
      ![L ((stdOrthonormalBasis ℝ X) i), L ((stdOrthonormalBasis ℝ X) i)] := by
    funext j
    fin_cases j <;> rfl
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def, hv] using hh'

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

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_eq_sum_directional {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y ((stdOrthonormalBasis ℝ X) i)) x
      ((stdOrthonormalBasis ℝ X) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply hf]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma compact_laplacian_continuous {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (Δ f) := by
  have he : Δ f = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y
      ((stdOrthonormalBasis ℝ X) i)) x ((stdOrthonormalBasis ℝ X) i) :=
    funext (laplacian_eq_sum_directional hf)
  rw [he]
  apply continuous_finsetSum
  intro i _
  have ht := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply (contDiff_const
    (c := (stdOrthonormalBasis ℝ X) i))
  exact (ht.continuous_fderiv (by simp)).clm_apply continuous_const

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_tsupport_subset {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (Δ f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  apply hx
  rw [laplacian_eq_sum_directional hf]
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hn ((tsupport_fderiv_apply_subset ℝ _ ) hh))]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma fderiv_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x v : X) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v)) x := by
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hs.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v

theorem laplacian_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x : X) :
    Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] Δ k) x := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  rw [laplacian_eq_sum_directional hc, convolution_mul]
  simp_rw [laplacian_eq_sum_directional hk, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    let v := (stdOrthonormalBasis ℝ X) i
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y v) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    have he : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v) :=
      funext (fun y ↦ fderiv_compact_convolution hf hk hs y v)
    change fderiv ℝ (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) x v = _
    rw [he, fderiv_compact_convolution hf hd (hs.fderiv_apply ℝ v)]
    rfl
  · intro i _
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y ((stdOrthonormalBasis ℝ X) i)) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hf
      ((hd.continuous_fderiv (by simp)).clm_apply continuous_const) x

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_translate {k : X → ℝ} (a x : X) :
    Δ (fun y ↦ k (a + y)) x = Δ k (a + x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_reflect_translate {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (a x : X) :
    Δ (fun y ↦ k (a - y)) x = Δ k (a - x) := by
  let L : X ≃ₗᵢ[ℝ] X := LinearIsometryEquiv.neg ℝ
  have hh := laplacian_comp_isometry L (hk.comp ((contDiff_const (c := a)).add contDiff_id)) x
  change Δ (fun y ↦ k (a + -y)) x = Δ (fun y ↦ k (a + y)) (-x) at hh
  rw [laplacian_translate] at hh
  simpa only [sub_eq_add_neg] using hh

theorem weak_harmonic_convolution {f k : X → ℝ} {Ω W : Set X}
    (hf : LocallyIntegrable f μ)
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y ∂μ) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    (hW : IsOpen W)
    (hkernel : ∀ x ∈ W, tsupport (fun y ↦ k (x - y)) ⊆ Ω) :
    InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) W := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  have hz (x : X) (hx : x ∈ W) : Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x = 0 := by
    rw [laplacian_compact_convolution hf hk hs, convolution_mul]
    have hp : HasCompactSupport (fun y ↦ k (x - y)) := by
      exact hs.comp_homeomorph (Homeomorph.subLeft x)
    have hh := hweak (fun y ↦ k (x - y)) (hk.comp (contDiff_const.sub contDiff_id)) hp
      (hkernel x hx)
    simpa only [laplacian_reflect_translate hk] using hh
  intro x hx
  refine ⟨(hc.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by norm_cast)).contDiffAt, ?_⟩
  filter_upwards [hW.mem_nhds hx] with y hy
  exact hz y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma harmonic_angular_integral {h : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c |r|)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) = 2 * Real.pi * h c := by
  have hm := hh.circleAverage_eq
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ ↦ h (circleMap c r θ))] at hm
  norm_num only [zero_add] at hm
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hm
  simp only [smul_eq_mul] at hm
  have hp : 2 * Real.pi ≠ 0 := by positivity
  calc
    _ = (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
        ∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) := by field_simp
    _ = _ := by rw [hm]

lemma add_polarCoord_eq_circleMap (c : ℂ) (r θ : ℝ) :
    c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, mul_add]

theorem harmonic_radial_mean {h : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (∫ z : ℂ, κ ‖z‖ * h (c + z)) = h c * ∫ z : ℂ, κ ‖z‖ := by
  let S : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  have hST : S ⊆ T := by intro p hp; exact ⟨hp.1.1, hp.2⟩
  have hTm : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hpcont : Continuous (Complex.polarCoord.symm) := by
    change Continuous (fun p : ℝ × ℝ ↦ _)
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hF : Continuous (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) :=
    continuous_fst.mul ((hk.comp continuous_fst.abs).mul
      (hh.comp (continuous_const.add hpcont)))
  have hG : Continuous (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) :=
    continuous_fst.mul (hk.comp continuous_fst.abs)
  have hSS : S ⊆ Icc (0, -Real.pi) (R, Real.pi) := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2, hp.2.2.le⟩⟩
  have hFi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) S :=
    hF.integrableOn_Icc.mono_set hSS
  have hGi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) S :=
    hG.integrableOn_Icc.mono_set hSS
  have hangle (r : ℝ) (hr : r ∈ Ioc 0 R) :
      (∫ θ in Ioo (-Real.pi) Real.pi, h (c + Complex.polarCoord.symm (r, θ))) =
        2 * Real.pi * h c := by
    simp_rw [add_polarCoord_eq_circleMap]
    apply harmonic_angular_integral
    apply harm.mono
    exact Metric.closedBall_subset_closedBall (by simpa only [abs_of_pos hr.1] using hr.2)
  rw [← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖ * h (c + z)),
    ← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖)]
  simp only [Complex.norm_polarCoord_symm, smul_eq_mul]
  change (∫ p in T, p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) =
    h c * ∫ p in T, p.1 * κ |p.1|
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_)]
  · simp only [Measure.volume_eq_prod] at hFi hGi ⊢
    dsimp only [S] at hFi hGi ⊢
    rw [setIntegral_prod _ hFi, setIntegral_prod _ hGi, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp_rw [← mul_assoc, integral_const_mul, hangle r hr]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi),
      smul_eq_mul]
    ring
  all_goals
    have hr : R < p.1 := by
      by_contra hn
      exact hp.2 ⟨⟨hp.1.1, le_of_not_gt hn⟩, hp.1.2⟩
    simp only [abs_of_pos (show 0 < p.1 from hp.1.1), hs p.1 hr, zero_mul, mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem exists_radial_smoothing_kernel {R : ℝ} (hR : 0 < R) :
    ∃ (k : ℂ → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) k ∧ HasCompactSupport k ∧
      (∀ z, k z = κ ‖z‖) ∧ Continuous κ ∧ (∀ r, R < r → κ r = 0) ∧
      tsupport k ⊆ Metric.closedBall 0 R ∧ (∫ z, k z) = 1 := by
  let b : ℂ → ℝ := fun z ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((2 / R) • z)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ ↦ ((2 : ℝ), (2 / R) • z)) :=
      contDiff_const.prodMk ((contDiff_const (c := (2 / R : ℝ))).smul contDiff_id)
    have ht : ∀ z : ℂ, ((2 : ℝ), (2 / R) • z) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set ℂ) :=
      fun _ ↦ ⟨by norm_num, mem_univ _⟩
    exact (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hg ht
  have hbformula (z : ℂ) : b z = Real.smoothTransition (2 - (2 / R) * ‖z‖) := by
    simp [b, ContDiffBumpBase.ofInnerProductSpace, Real.norm_eq_abs, abs_of_pos hR, show (2 : ℝ) - 1 = 1 from by norm_num]
  have hzero (r : ℝ) (hr : R < r) : Real.smoothTransition (2 - (2 / R) * r) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have hh : 2 < (2 / R) * r := by
      have := (mul_lt_mul_of_pos_left hr (by positivity : 0 < 2 / R))
      field_simp at this ⊢
      nlinarith
    linarith
  have hbs : tsupport b ⊆ Metric.closedBall 0 R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    by_contra hn
    have hr : R < ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
    exact hz (by rw [hbformula, hzero _ hr])
  have hbc : HasCompactSupport b := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hbs
  have hbpos : 0 < ∫ z, b z := by
    apply hb.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc
      (fun _ ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _ |>.1)
    rw [hbformula 0]
    norm_num [Real.smoothTransition.one_of_one_le]
  let k : ℂ → ℝ := fun z ↦ b z / ∫ y, b y
  let κ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 - (2 / R) * r) / ∫ y, b y
  have hks : tsupport k ⊆ Metric.closedBall 0 R := by
    change tsupport (fun z ↦ b z * (∫ y, b y)⁻¹) ⊆ _
    exact tsupport_mul_subset_left.trans hbs
  have hkc : HasCompactSupport k := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hks
  refine ⟨k, κ, hb.div_const _, hkc, ?_, ?_, ?_, hks, ?_⟩
  · intro z
    exact congrArg (fun t : ℝ ↦ t / ∫ y, b y) (hbformula z)
  · exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub (continuous_const.mul continuous_id))).div_const _
  · intro r hr
    simp only [κ, hzero r hr, zero_div]
  · dsimp only [k]
    rw [integral_div, div_self hbpos.ne']

lemma harmonic_radial_convolution {h k : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (h ⋆[ContinuousLinearMap.mul ℝ ℝ] k) c = h c := by
  rw [convolution_eq_swap, ← integral_neg_eq_self]
  simp only [ContinuousLinearMap.mul_apply']
  simp only [hk, norm_neg, sub_neg_eq_add, mul_comm (h _)]
  rw [harmonic_radial_mean hh hc hs harm]
  have hi' : (∫ z : ℂ, κ ‖z‖) = 1 := by simpa only [hk] using hi
  rw [hi', mul_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma real_convolution_comm (f g : X → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] f := by
  ext x
  rw [convolution_mul_swap, convolution_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ mul_comm _ _)

lemma compact_convolution_assoc {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k)) x := by
  apply convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c) hf.aestronglyMeasurable
    hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hgs.convolutionExists_right _ hf hg)
  · exact Eventually.of_forall (hks.norm.convolutionExists_right _ hg.norm.locallyIntegrable hk.norm)
  · exact (hgs.norm.convolution (ContinuousLinearMap.mul ℝ ℝ) hks.norm).convolutionExists_right _
      (fun x ↦ (hf x).norm) (hks.norm.continuous_convolution_right _ hg.norm.locallyIntegrable hk.norm) x

lemma compact_convolutions_commute {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) x := by
  rw [compact_convolution_assoc hf hg hgs hk hks,
    compact_convolution_assoc hf hk hks hg hgs, real_convolution_comm g k]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in

lemma reflected_tsupport_subset_ball {k : X → ℝ} {c x : X} {r R : ℝ}
    (hk : tsupport k ⊆ Metric.closedBall 0 r) (hx : dist x c + r < R) :
    tsupport (fun y ↦ k (x - y)) ⊆ Metric.ball c R := by
  have hs : tsupport (fun y ↦ k (x - y)) ⊆
      (fun y ↦ x - y) ⁻¹' tsupport k := tsupport_comp_subset_preimage k (by fun_prop)
  intro y hy
  have ht := hk (hs hy)
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at ht
  rw [Metric.mem_ball]
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ = dist x y + dist x c := by rw [dist_comm y x]
    _ ≤ r + dist x c := by linarith
    _ < R := by linarith

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
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma planarMollifier_tendsto : Tendsto (fun i ↦ (planarMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [planarMollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma planarMollifier_ratio (i : ℕ) :
    (planarMollifier i).rOut ≤ 2 * (planarMollifier i).rIn := by
  dsimp only [planarMollifier]
  rw [mul_div, mul_one]

theorem weak_harmonic_radial_reproduction {f k : ℂ → ℝ} {κ : ℝ → ℝ}
    {Ω : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball c (4 * R) ⊆ Ω) (hf : LocallyIntegrable f)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hrad : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hκ : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1) :
    f =ᵐ[volume.restrict (Metric.ball c R)] f ⋆[ContinuousLinearMap.mul ℝ ℝ] k := by
  let p (i : ℕ) : ℂ → ℝ := (planarMollifier i).normed volume
  let u : ℂ → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hu : Continuous u := hks.continuous_convolution_right _ hf hk.continuous
  have hp (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (p i) := (planarMollifier i).contDiff_normed
  have hps (i : ℕ) : HasCompactSupport (p i) := (planarMollifier i).hasCompactSupport_normed
  have hsmall : ∀ᶠ i in atTop, (planarMollifier i).rOut < R :=
    planarMollifier_tendsto.eventually (gt_mem_nhds hR)
  have hharm (i : ℕ) (hiR : (planarMollifier i).rOut < R) :
      InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i)
        (Metric.ball c (3 * R)) := by
    apply weak_harmonic_convolution hf hweak (hp i) (hps i) Metric.isOpen_ball
    intro x hx
    apply Subset.trans _ hball
    apply reflected_tsupport_subset_ball
      (le_of_eq ((planarMollifier i).tsupport_normed_eq (μ := volume)))
    have hx' : dist x c < 3 * R := hx
    linarith
  have he (x : ℂ) (hx : x ∈ Metric.ball c R) :
      ∀ᶠ i in atTop, (u ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x =
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x := by
    filter_upwards [hsmall] with i hiR
    rw [← compact_convolutions_commute hf (hp i).continuous (hps i) hk.continuous hks]
    apply harmonic_radial_convolution
      ((hps i).continuous_convolution_right _ hf (hp i).continuous) hrad hc hκ hi
    apply (hharm i hiR).mono
    intro y hy
    have hy' : dist y x ≤ R := hy
    have hx' : dist x c < R := hx
    change dist y c < 3 * R
    have ht := dist_triangle y x c
    linarith
  have hfa := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    planarMollifier_tendsto (Eventually.of_forall planarMollifier_ratio) hf
  filter_upwards [ae_restrict_of_ae hfa, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hua := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) planarMollifier_tendsto hu x
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) atTop (𝓝 (f x)) at hx
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x) atTop (𝓝 (u x)) at hua
  simp_rw [real_convolution_comm (p _) f] at hx
  simp_rw [real_convolution_comm (p _) u] at hua
  exact tendsto_nhds_unique hx (hua.congr' (he x hxball))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma second_deriv_convolution_le {f k : X → ℝ} (hf : Integrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖ ≤ C) (x : X) :
    ‖fderiv ℝ (fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k)) x‖ ≤
      C * ∫ y, ‖f y‖ ∂μ := by
  let u : X → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hs.contDiff_convolution_right _ hf.locallyIntegrable hk
  have hm : 0 ≤ ∫ y, ‖f y‖ ∂μ := integral_nonneg (fun _ ↦ norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hm)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ fderiv ℝ k z w) :=
    (hk.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun z ↦ fderiv ℝ u z w) =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun z ↦ fderiv ℝ k z w) :=
    funext (fun z ↦ fderiv_compact_convolution hf.locallyIntegrable hk hs z w)
  rw [← fderiv_fderiv_apply hu, he,
    fderiv_compact_convolution hf.locallyIntegrable hd (hs.fderiv_apply ℝ w), convolution_mul]
  have hi : Integrable (fun t ↦ (C * ‖v‖ * ‖w‖) * ‖f t‖) μ := hf.norm.const_mul _
  calc
    _ ≤ ∫ t, (C * ‖v‖ * ‖w‖) * ‖f t‖ ∂μ := by
      apply norm_integral_le_of_norm_le hi
      exact Eventually.of_forall fun t ↦ by
        rw [norm_mul, fderiv_fderiv_apply hk]
        have hb' : ‖(fderiv ℝ (fderiv ℝ k) (x - t) v) w‖ ≤ C * ‖v‖ * ‖w‖ := by
          calc
            _ ≤ ‖fderiv ℝ (fderiv ℝ k) (x - t) v‖ * ‖w‖ :=
              (fderiv ℝ (fderiv ℝ k) (x - t) v).le_opNorm w
            _ ≤ (‖fderiv ℝ (fderiv ℝ k) (x - t)‖ * ‖v‖) * ‖w‖ := by
              gcongr
              exact (fderiv ℝ (fderiv ℝ k) (x - t)).le_opNorm v
            _ ≤ _ := by gcongr; exact hb (x - t)
        calc
          _ ≤ ‖f t‖ * (C * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := by rw [integral_const_mul]; ring

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_compact_norm_bound {Y : Type*} [NormedAddCommGroup Y]
    {g : X → Y} (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hs.norm
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma smooth_compact_hessian_bound {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖ ≤ C := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) := hk.fderiv_right (by simp)
  have hd₂ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ k)) := hd.fderiv_right (by simp)
  exact continuous_compact_norm_bound hd₂.continuous ((hs.fderiv ℝ).fderiv ℝ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma weak_harmonic_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} {R : ℝ}
    (hf : ∀ φ : Y → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, f y * Δ φ y) = 0) :
    ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, (f ∘ L) y * Δ φ y) = 0 := by
  intro φ hφ hs hb
  have hsupport : tsupport (φ ∘ L.symm) ⊆ Metric.ball 0 R := by
    rw [show tsupport (φ ∘ L.symm) = L.symm ⁻¹' tsupport φ from
      tsupport_comp_eq_preimage φ L.symm.toHomeomorph]
    intro y hy
    have hh := hb hy
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
  have hh := hf (φ ∘ L.symm) (hφ.comp L.symm.contDiff)
    (hs.comp_homeomorph L.symm.toHomeomorph) hsupport
  rw [← L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding] at hh
  simpa only [Function.comp_apply, laplacian_comp_isometry L.symm hφ,
    LinearIsometryEquiv.symm_apply_apply] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma L2_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ ↦ by simp [pow_two]

lemma L2_toLp_dist_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 μ) (u : Lp ℝ 2 μ) :
    dist (hf.toLp f) u ^ 2 = ∫ x, (f x - u x) ^ 2 ∂μ := by
  rw [dist_eq_norm, L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) u, hf.coeFn_toLp] with x hx hxf
  simp only [hx, Pi.sub_apply, hxf]

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

theorem L2_weak_harmonic_limit {K Ω : Set Plane} (hK : IsCompact K) (hΩ : Ω ⊆ K)
    {f : ℕ → Plane → ℝ} (hf : ∀ i, MemLp (f i) 2 (volume.restrict K))
    {u : Lp ℝ 2 (volume.restrict K)}
    (hu : Tendsto (fun i ↦ (hf i).toLp (f i)) atTop (𝓝 u))
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, K.indicator (fun x ↦ u x) y * Δ φ y) = 0 := by
  intro φ hφ hs hb
  have hlaps : HasCompactSupport (Δ φ) := hs.mono' ((subset_tsupport _).trans (laplacian_tsupport_subset hφ))
  have hlap : MemLp (Δ φ) 2 (volume.restrict K) :=
    (compact_laplacian_continuous hφ).memLp_of_hasCompactSupport hlaps
  let v := hlap.toLp (Δ φ)
  have hpair (i : ℕ) : (∫ x, ((hf i).toLp (f i)) x * v x ∂volume.restrict K) =
      ∫ x, f i x * Δ φ x := by
    rw [integral_mul_eq_restrict_of_tsupport hK.measurableSet (f i) (Δ φ)
      ((laplacian_tsupport_subset hφ).trans (hb.trans hΩ))]
    apply integral_congr_ae
    filter_upwards [(hf i).coeFn_toLp, hlap.coeFn_toLp] with x hx hv
    rw [hx, hv]
  have hz := L2_pairing_limit_zero hu v (by simpa only [hpair] using hw φ hφ hs hb)
  calc
    _ = ∫ x in K, u x * Δ φ x := by
      rw [← integral_indicator hK.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by simp only [indicator_mul_left]
    _ = ∫ x, u x * v x ∂volume.restrict K := by
      apply integral_congr_ae
      filter_upwards [hlap.coeFn_toLp] with x hx
      rw [hx]
    _ = 0 := hz

lemma L2_zero_extension_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (u : Lp ℝ 2 (μ.restrict K)) :
    Integrable (K.indicator (fun x ↦ u x)) μ ∧
      (∫ x, ‖K.indicator (fun y ↦ u y) x‖ ∂μ) ^ 2 ≤ μ.real K * ‖u‖ ^ 2 := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hfin
  have hi : Integrable (fun x ↦ u x) (μ.restrict K) := MemLp.integrable (by norm_num) (Lp.memLp u)
  have hs : Integrable (fun x ↦ ‖u x‖ ^ 2) (μ.restrict K) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  refine ⟨IntegrableOn.integrable_indicator hi hK, ?_⟩
  have he : (fun x ↦ ‖K.indicator (fun y ↦ u y) x‖) = K.indicator (fun x ↦ ‖u x‖) := by
    funext x
    simp only [norm_indicator_eq_indicator_norm]
  rw [he, integral_indicator hK, L2_norm_sq_integral]
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.norm_eq_abs, sq_abs] using
    integral_square_le_mass hi.norm hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fderiv_mul_sq_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y ↦ f y * g y) x‖ ^ 2 ≤
      2 * f x ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + 2 * g x ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
  change ‖fderiv ℝ (f * g) x‖ ^ 2 ≤ _
  rw [fderiv_mul hf hg]
  have hb := norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)
  simp only [norm_smul, Real.norm_eq_abs] at hb
  have ha := norm_nonneg (f x • fderiv ℝ g x + g x • fderiv ℝ f x)
  nlinarith [sq_abs (f x), sq_abs (g x),
    sq_nonneg (|f x| * ‖fderiv ℝ g x‖ - |g x| * ‖fderiv ℝ f x‖)]

lemma fderiv_mul_sq_bound_of_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f ζ : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hζ : DifferentiableAt ℝ ζ x)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |ζ x| ≤ A) (hb : ‖fderiv ℝ ζ x‖ ≤ B) :
    ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2 ≤
      2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2 := by
  have hp := fderiv_mul_sq_bound hζ hf
  have hz : ζ x ^ 2 ≤ A ^ 2 := by nlinarith [sq_abs (ζ x), abs_nonneg (ζ x)]
  have hd : ‖fderiv ℝ ζ x‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg (fderiv ℝ ζ x)]
  nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg ‖fderiv ℝ f x‖),
    mul_le_mul_of_nonneg_left hd (sq_nonneg (f x))]

lemma integrable_integral_le_of_support_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} {u q : X → ℝ}
    (hu : AEStronglyMeasurable u μ) (hq : IntegrableOn q S μ)
    (hzero : ∀ x ∉ S, u x = 0)
    (hb : ∀ᵐ x ∂μ.restrict S, |u x| ≤ q x) :
    Integrable u μ ∧ (∫ x, u x ∂μ) ≤ ∫ x in S, q x ∂μ := by
  have hi : IntegrableOn u S μ := hq.mono' hu.restrict (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨hi.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact integral_mono_ae hi hq (hb.mono fun x hx ↦ (le_abs_self (u x)).trans hx)

theorem lipschitz_cutoff_H1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f ζ : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hζ : ContDiff ℝ 1 ζ) (_hs : HasCompactSupport ζ)
    {S : Set X} (hS : IsCompact S) (hsub : tsupport ζ ⊆ S)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, |ζ x| ≤ A) (hb : ∀ x, ‖fderiv ℝ ζ x‖ ≤ B) :
    Integrable (fun x ↦ (ζ x * f x) ^ 2) μ ∧
    Integrable (fun x ↦ ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2) μ ∧
    (∫ x, (ζ x * f x) ^ 2 ∂μ) ≤ A ^ 2 * ∫ x in S, f x ^ 2 ∂μ ∧
    (∫ x, ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2 ∂μ) ≤
      2 * A ^ 2 * (∫ x in S, ‖fderiv ℝ f x‖ ^ 2 ∂μ) +
        2 * B ^ 2 * (∫ x in S, f x ^ 2 ∂μ) := by
  have hfs : IntegrableOn (fun x ↦ f x ^ 2) S μ :=
    ContinuousOn.integrableOn_compact hS (hf.continuous.pow 2).continuousOn
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hdf := lipschitz_fderiv_sq_integrable (μ := μ.restrict S) hf
  have hzero (x : X) (hx : x ∉ S) : ζ x * f x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsub h)), zero_mul]
  have hdzero (x : X) (hx : x ∉ S) : fderiv ℝ (fun y ↦ ζ y * f y) x = 0 := by
    apply fderiv_of_notMem_tsupport ℝ
    intro h
    exact hx (hsub (tsupport_mul_subset_left h))
  have hi := integrable_integral_le_of_support_bound
    (u := fun x ↦ (ζ x * f x) ^ 2) (q := fun x ↦ A ^ 2 * f x ^ 2)
    ((hζ.continuous.mul hf.continuous).pow 2).aestronglyMeasurable (hfs.const_mul (A ^ 2))
    (fun x hx ↦ by simp only [hzero x hx, zero_pow (by norm_num : 2 ≠ 0)]) (by
      apply Eventually.of_forall
      intro x
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh : ζ x ^ 2 ≤ A ^ 2 := by nlinarith [ha x, sq_abs (ζ x), abs_nonneg (ζ x)]
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (f x))])
  have hid := integrable_integral_le_of_support_bound (μ := μ) (S := S)
    (u := fun x ↦ ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2)
    (q := fun x ↦ 2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2)
    ((measurable_fderiv ℝ (fun y ↦ ζ y * f y)).norm.pow_const 2).aestronglyMeasurable
    (show IntegrableOn (fun x ↦ 2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2) S μ from
      (hdf.const_mul (2 * A ^ 2)).add (hfs.const_mul (2 * B ^ 2)))
    (fun x hx ↦ by simp only [hdzero x hx, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]) (by
      filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt] with x hx
      simp only [abs_pow, abs_norm]
      exact fderiv_mul_sq_bound_of_bounds hx (hζ.differentiable (by norm_num) x) hA hB (ha x) (hb x))
  refine ⟨hi.1, hid.1, ?_, ?_⟩
  · simpa only [integral_const_mul] using hi.2
  · simpa only [integral_add (hdf.const_mul _) (hfs.const_mul _), integral_const_mul] using hid.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

lemma isCompact_planeSquare (R : ℝ) : IsCompact (planeSquare R) :=
  planeProductCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)

lemma planeSquare_measurePreserving (R : ℝ) :
    MeasurePreserving planeProductCoordinates
      (volume.restrict (planeSquare R))
      ((volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc (-R) R))) := by
  have h := planeProductCoordinates_measurePreserving.restrict_preimage
    (s := Icc (-R) R ×ˢ Icc (-R) R)
    (measurableSet_Icc.prod measurableSet_Icc)
  simpa only [planeSquare, Measure.prod_restrict, ← Measure.volume_eq_prod] using h

theorem plane_square_poincare {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {R : ℝ} (hR : 0 < R) :
    (∫ x in planeSquare R,
      (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2) ^ 2) ≤
      16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 *
        (∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) := by
  let L := planeProductCoordinates.symm
  let ν := (volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc (-R) R))
  have hL : MeasurePreserving L ν (volume.restrict (planeSquare R)) :=
    (planeSquare_measurePreserving R).symm planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLip : LipschitzWith (K * ‖L.toContinuousLinearMap‖₊) (f ∘ L) :=
    hf.comp L.toContinuousLinearMap.lipschitz
  have hp := lipschitz_box_poincare_fderiv hLip (by linarith : -R < R)
  change (∫ x, (f (L x) - (∫ y, f (L y) ∂ν) / (R - -R) ^ 2) ^ 2 ∂ν) ≤
    4 * (R - -R) ^ 2 * ∫ x, ‖fderiv ℝ (f ∘ L) x‖ ^ 2 ∂ν at hp
  have hmean := hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding f
  rw [hmean] at hp
  have hh := hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x ↦ (f x - (∫ y in planeSquare R, f y) / (R - -R) ^ 2) ^ 2)
  rw [hh] at hp
  have hleft : (∫ x, ‖fderiv ℝ (f ∘ L) x‖ ^ 2 ∂ν) ≤
      ‖L.toContinuousLinearMap‖ ^ 2 * ∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2 := by
    let : IsFiniteMeasure (volume.restrict (planeSquare R)) :=
      isFiniteMeasure_restrict.mpr (isCompact_planeSquare R).measure_lt_top.ne
    have hd : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (volume.restrict (planeSquare R)) :=
      lipschitz_fderiv_sq_integrable hf
    have hdL := (hL.integrable_comp hd.aestronglyMeasurable).mpr hd
    have hi := lipschitz_fderiv_sq_integrable (μ := ν) hLip
    have he := integral_mono_ae hi (hdL.const_mul (‖L.toContinuousLinearMap‖ ^ 2)) (by
      filter_upwards [hL.quasiMeasurePreserving.ae (ae_restrict_of_ae hf.ae_differentiableAt)] with x hx
      rw [fderiv_comp x hx L.differentiableAt, L.fderiv]
      have hb := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (L x)) L.toContinuousLinearMap
      have hpos := norm_nonneg ((fderiv ℝ f (L x)).comp L.toContinuousLinearMap)
      have hs := pow_le_pow_left₀ hpos hb 2
      simpa only [Function.comp_apply, mul_pow, mul_comm] using hs)
    simp only [integral_const_mul, Function.comp_apply] at he
    rw [hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x ↦ ‖fderiv ℝ f x‖ ^ 2)] at he
    exact he
  have he := mul_le_mul_of_nonneg_left hleft (by positivity : 0 ≤ 4 * (R - -R) ^ 2)
  have he' := hp.trans he
  have hr : R - -R = 2 * R := by ring
  rw [hr] at he'
  calc
    _ ≤ 4 * (2 * R) ^ 2 * (‖L.toContinuousLinearMap‖ ^ 2 *
        ∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) := he'
    _ = _ := by dsimp [L]; ring

lemma planeSquare_volume (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure Plane).real (planeSquare R) = (2 * R) ^ 2 := by
  have h := planeProductCoordinates_measurePreserving.measure_preimage
    (s := Icc (-R) R ×ˢ Icc (-R) R)
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
  change (volume : Measure Plane) (planeSquare R) = _ at h
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc] at h
  rw [measureReal_def, h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
  ring

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma measurable_normalColumnHeight {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) : Measurable (normalColumnHeight U a n r) := by
  have hc : Continuous (fun p : Plane × ℝ ↦
      a + quotientMap (normalPlaneEmbedding n p.1 + p.2 • n)) :=
    continuous_const.add (continuous_quotientMap.comp
      (((normalPlaneLinearIsometry n).continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)))
  exact (((measurable_characteristic hU).comp hc.measurable).stronglyMeasurable.integral_prod_right').measurable.sub_const _

lemma normalColumn_integrable {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (y : Plane) :
    IntegrableOn (fun t ↦ characteristic U
      (a + quotientMap (normalPlaneEmbedding n y + t • n))) (Icc (-r / 4) (r / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_characteristic hU).comp
      (continuous_const.add (continuous_quotientMap.comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U _

end CubicTorus

end
end

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
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
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma measurableSet_torusGraphRegion (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    MeasurableSet (torusGraphRegion a n g) := by
  apply measurableSet_lt
  · exact measurable_const.inner (measurable_representative.sub_const a)
  · exact (hg.comp ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub continuous_const))).measurable.comp measurable_representative

lemma characteristic_torusGraphRegion {x : Cover} (hx : x ∈ fundamentalCube)
    (a n : Cover) (g : Plane → ℝ) :
    characteristic (torusGraphRegion a n g) (quotientMap x) = graphSublevelIndicator a n g x := by
  simp only [characteristic, torusGraphRegion, Set.indicator, Set.mem_ofPred_eq,
    representative_quotientMap_of_mem hx, graphSublevelIndicator]

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

lemma lipschitz_probability_average_gradient_sq {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2 ≤ ∫ y, ‖fderiv ℝ f (x-y)‖^2 ∂ν := by
  have hh := lipschitz_probability_average_hasFDerivAt hν hf hδ hb x
  rw [hh.2.fderiv]
  have hi : Integrable (fun y ↦ ‖fderiv ℝ f (x-y)‖^2) ν := by
    apply (integrable_const ((K : ℝ)^2)).mono'
      (((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖fderiv ℝ f (x-y)‖^2 ≤ (K : ℝ)^2
    have hb' := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x-y)
    nlinarith [norm_nonneg (fderiv ℝ f (x-y))]
  have hs := integral_square_le_mass hh.1.norm hi
  simp only [probReal_univ, one_mul] at hs
  have hn := norm_integral_le_integral_norm (μ := ν) (fun y ↦ fderiv ℝ f (x-y))
  have hi0 : 0 ≤ ∫ y, ‖fderiv ℝ f (x-y)‖ ∂ν := integral_nonneg (fun y ↦ norm_nonneg _)
  nlinarith [norm_nonneg (∫ y, fderiv ℝ f (x-y) ∂ν)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_gradient_sq_integrable_ball {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ f x‖^2) (Metric.ball (0 : Plane) R) := by
  apply (integrableOn_const (C := (K : ℝ)^2) measure_ball_lt_top.ne).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable.restrict
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2

lemma lipschitz_gradient_sq_shift_ball_le {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R δ : ℝ) {y : Plane} (hy : ‖y‖ ≤ δ) :
    (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ f (x-y)‖^2) ≤
      ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2 := by
  let G : Plane → ℝ := (Metric.ball (0 : Plane) (R+δ)).indicator (fun x ↦ ‖fderiv ℝ f x‖^2)
  have hi : Integrable G := (lipschitz_gradient_sq_integrable_ball hf (R+δ)).integrable_indicator
    measurableSet_ball
  have hit : Integrable (fun x ↦ G (x-y)) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      ((measurePreserving_add_right volume (-y)).integrable_comp hi.aestronglyMeasurable).mpr hi
  have hil : IntegrableOn (fun x ↦ ‖fderiv ℝ f (x-y)‖^2) (Metric.ball (0 : Plane) R) := by
    apply (integrableOn_const (C := (K : ℝ)^2) measure_ball_lt_top.ne).mono'
      (((measurable_fderiv ℝ f).comp (measurable_id.sub_const y)).norm.pow_const 2).aestronglyMeasurable.restrict
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖fderiv ℝ f (x-y)‖^2 ≤ (K : ℝ)^2
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
  rw [← integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫ x : Plane, G (x-y) := by
      apply integral_mono (hil.integrable_indicator measurableSet_ball) hit
      intro x
      by_cases hx : x ∈ Metric.ball (0 : Plane) R
      · have hxy : x-y ∈ Metric.ball (0 : Plane) (R+δ) := by
          rw [Metric.mem_ball, dist_zero_right] at hx ⊢
          exact (norm_sub_le x y).trans_lt (add_lt_add_of_lt_of_le hx hy)
        simp only [indicator_of_mem hx, G, indicator_of_mem hxy, le_refl]
      · rw [indicator_of_notMem hx]
        exact indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
    _ = _ := by
      rw [show (fun x : Plane ↦ G (x-y)) = (fun x ↦ G (x+(-y))) from rfl,
        integral_add_right_eq_self G (-y)]
      exact integral_indicator measurableSet_ball

theorem lipschitz_probability_average_local_energy {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) (Metric.ball (0 : Plane) R) ∧
      (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2 := by
  let μ : Measure Plane := volume.restrict (Metric.ball (0 : Plane) R)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let H : Plane × Plane → ℝ := fun p ↦ ‖fderiv ℝ f (p.2-p.1)‖^2
  have hHm : Measurable H := ((measurable_fderiv ℝ f).comp (measurable_snd.sub measurable_fst)).norm.pow_const 2
  have hH : Integrable H (ν.prod μ) := by
    apply (integrable_const ((K : ℝ)^2)).mono' hHm.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
  have hpoint (x : Plane) : ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2 ≤ ∫ y, H (y,x) ∂ν :=
    lipschitz_probability_average_gradient_sq hν hf hδ hb x
  have hI : Integrable (fun x ↦ ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) μ := by
    apply hH.integral_prod_right.mono'
      ((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, H (y,x) ∂ν ∂μ := integral_mono hI hH.integral_prod_right hpoint
    _ = ∫ y, ∫ x, H (y,x) ∂μ ∂ν := integral_integral_swap hH.swap
    _ ≤ ∫ _y : Plane, (∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2) ∂ν := by
      apply integral_mono_ae hH.integral_prod_left (integrable_const _)
      filter_upwards [hb] with y hy
      exact lipschitz_gradient_sq_shift_ball_le hf R δ hy
    _ = _ := by simp

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

lemma graphSmooth_local_energy (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ (graphSmooth b f) x‖^2) (Metric.ball (0 : Plane) R) ∧
      (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ (graphSmooth b f) x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+b.rOut), ‖fderiv ℝ f x‖^2 :=
  lipschitz_probability_average_local_energy (graphSmoothingMeasure_ac b) hf b.rOut_pos.le
    (graphSmoothingMeasure_radius b) R

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVOrientedGraphCost
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
open Laplacian
namespace CubicTorus

lemma compact_convolution_gradient_lipschitz {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℝ, Integrable f μ → ∀ x y : X,
      let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
      ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C*(∫ z, ‖f z‖ ∂μ)*‖x-y‖ := by
  obtain ⟨C,hC,hbound⟩ := smooth_compact_hessian_bound hk hs
  refine ⟨C,hC,fun f hf x y ↦ ?_⟩
  let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hs.contDiff_convolution_right _ hf.locallyIntegrable hk
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by simp)
  exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hd.differentiable (by simp) |>.differentiableAt)
    (fun z _ ↦ second_deriv_convolution_le hf hk hs hC.le hbound z)
    (mem_univ y) (mem_univ x)

theorem plane_weak_harmonic_smooth_representative {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Plane → ℝ, Integrable f →
      (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4*R) → (∫ y, f y * Δ φ y) = 0) →
      ∃ u : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧
        f =ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        ∀ x y : Plane, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ C*(∫ z, ‖f z‖)*‖x-y‖ := by
  let L := Complex.orthonormalBasisOneI.repr
  obtain ⟨k,κ,hk,hks,hrad,hc,hκ,_,hi⟩ := exists_radial_smoothing_kernel hR
  obtain ⟨C,hC,hgrad⟩ := compact_convolution_gradient_lipschitz (μ := volume) hk hks
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let v := (f ∘ L) ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hfL : Integrable (f ∘ L) := (L.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hks.contDiff_convolution_right _ hfL.locallyIntegrable hk
  refine ⟨v ∘ L.symm,hv.comp L.symm.contDiff,?_,?_⟩
  · have he := weak_harmonic_radial_reproduction hR (Subset.refl _) hfL.locallyIntegrable
      (weak_harmonic_comp_isometry L hw) hk hks hrad hc hκ hi
    have hmp : MeasurePreserving L.symm
        (volume.restrict (Metric.ball (0 : Plane) R))
        (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      simpa only [L.symm.preimage_ball, map_zero] using
        L.symm.measurePreserving.restrict_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := R))
    have hh := hmp.quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [hh] with z hz
    change f (L (L.symm z)) = v (L.symm z) at hz
    change f z = v (L.symm z)
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hz
  · intro x y
    have he (z : Plane) : fderiv ℝ (v ∘ L.symm) z =
        (fderiv ℝ v (L.symm z)).comp L.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
      rw [fderiv_comp z (hv.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
      congr 1
      exact L.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
    rw [he x, he y, ← ContinuousLinearMap.sub_comp]
    have hh : ‖L.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
      exact L.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    calc
      _ ≤ ‖fderiv ℝ v (L.symm x)-fderiv ℝ v (L.symm y)‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hh)
      _ ≤ C*(∫ z, ‖(f ∘ L) z‖)*‖L.symm x-L.symm y‖ := hgrad _ hfL _ _
      _ = _ := by
        rw [← map_sub, L.symm.norm_map]
        dsimp only [Function.comp_def]
        rw [L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding (fun z ↦ ‖f z‖)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma plane_gradient_oscillation_energy {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hb : ∀ x : Plane, ‖fderiv ℝ u x-fderiv ℝ u 0‖ ≤ A*‖x‖) :
    (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) ≤ Real.pi*A^2*ρ^4 := by
  have hi : IntegrableOn (fun x ↦ ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) (Metric.ball (0 : Plane) ρ) :=
    (((hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) ρ) |>.mono_set Metric.ball_subset_closedBall
  have hpoint : ∀ x ∈ Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2 ≤ A^2*ρ^2 := by
    intro x hx
    have hxρ : ‖x‖ ≤ ρ := by simpa only [dist_zero_right] using (show dist x 0 < ρ from hx).le
    calc
      _ ≤ (A*‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
      _ ≤ (A*ρ)^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫ _ in Metric.ball (0 : Plane) ρ, A^2*ρ^2 := by
      apply integral_mono_ae hi (integrableOn_const measure_ball_lt_top.ne)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hpoint x hx
    _ = _ := by
      rw [integral_const, smul_eq_mul, show (volume.restrict (Metric.ball (0 : Plane) ρ)).real univ =
        volume.real (Metric.ball (0 : Plane) ρ) by simp [Measure.real], plane_ball_real hρ]
      ring

theorem planar_H1_strong_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {K : Set Plane} (hK : IsCompact K) (hball : Metric.ball (0 : Plane) (4*R) ⊆ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
      (∀ i, LipschitzWith (L i) (f i)) →
      (∀ i, Integrable (fun x ↦ f i x^2)) →
      (∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖^2)) →
      ∀ M D : ℝ, 0 ≤ D → (∀ i, (∫ x, f i x^2) ≤ M) →
      (∀ i, (∫ x, ‖fderiv ℝ (f i) x‖^2) ≤ D) →
      (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4*R) → Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (u : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-u x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨C₀,hC₀,hsmooth⟩ := plane_weak_harmonic_smooth_representative hR
  let vK := (volume : Measure Plane).real K
  refine ⟨Real.pi*C₀^2*(vK+1), by dsimp [vK]; positivity, ?_⟩
  intro f L hf hfs hgrad M D hD hM hbound hw
  obtain ⟨u,ψ,hψ,hmem,hu⟩ := restricted_H1_subsequence hK f L hf hfs hgrad hD hM hbound
  have hM0 : 0 ≤ M := (integral_nonneg fun x ↦ sq_nonneg (f 0 x)).trans (hM 0)
  have hnorm : ‖u‖^2 ≤ M := by
    apply le_of_tendsto (hu.norm.pow 2)
    exact Eventually.of_forall fun i ↦ by
      rw [L2_norm_sq_integral]
      calc
        _ = ∫ x in K, f (ψ i) x^2 := integral_congr_ae ((hmem (ψ i)).coeFn_toLp.mono fun x hx ↦ by rw [hx])
        _ ≤ ∫ x, f (ψ i) x^2 := integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun x ↦ sq_nonneg _) (hfs (ψ i))
        _ ≤ M := hM (ψ i)
  let U : Plane → ℝ := K.indicator (fun x ↦ u x)
  have hU := L2_zero_extension_bounds hK.measurableSet hK.measure_lt_top.ne u
  have hweak := L2_weak_harmonic_limit hK hball (fun i ↦ hmem (ψ i)) hu
    (fun φ hφ hs hb ↦ (hw φ hφ hs hb).comp hψ.tendsto_atTop)
  obtain ⟨v,hv,he,hvgrad⟩ := hsmooth U hU.1 hweak
  have hRK : Metric.ball (0 : Plane) R ⊆ K :=
    (Metric.ball_subset_ball (by linarith : R ≤ 4*R)).trans hball
  have hueq : (fun x ↦ u x) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] v := by
    filter_upwards [he,ae_restrict_mem measurableSet_ball] with x hx hxR
    rw [show U x = u x from indicator_of_mem (hRK hxR) _] at hx
    exact hx
  refine ⟨ψ,v,hψ,hv,?_,?_⟩
  · have hsmall : Tendsto (fun i ↦ ∫ x in K, (f (ψ i) x-u x)^2) atTop (𝓝 0) := by
      have hh := (hu.dist (tendsto_const_nhds (x := u))).pow 2
      simpa only [dist_self, zero_pow (by norm_num : 2 ≠ 0), L2_toLp_dist_sq] using hh
    apply squeeze_zero (fun i ↦ integral_nonneg fun x ↦ sq_nonneg _) (fun i ↦ ?_) hsmall
    calc
      _ = ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-u x)^2 :=
        integral_congr_ae (hueq.mono fun x hx ↦ by dsimp only at hx ⊢; rw [hx])
      _ ≤ _ := integral_mono_measure (Measure.restrict_mono hRK le_rfl)
        (Eventually.of_forall fun x ↦ sq_nonneg _)
        ((memLp_two_iff_integrable_sq ((hmem (ψ i)).sub (Lp.memLp u)).aestronglyMeasurable).mp
          ((hmem (ψ i)).sub (Lp.memLp u)))
  · intro ρ hρ
    have hi0 : 0 ≤ ∫ z, ‖U z‖ := integral_nonneg fun z ↦ norm_nonneg _
    have hb : (∫ z, ‖U z‖)^2 ≤ vK*M := hU.2.trans (mul_le_mul_of_nonneg_left hnorm measureReal_nonneg)
    have hh := plane_gradient_oscillation_energy hv (mul_nonneg hC₀.le hi0) hρ
      (fun x ↦ by simpa only [sub_zero] using hvgrad x 0)
    apply hh.trans
    have hnon : 0 ≤ Real.pi*C₀^2*ρ^4 := by positivity
    have hc := mul_le_mul_of_nonneg_left hb hnon
    have hadd : 0 ≤ Real.pi*C₀^2*M*ρ^4 := by positivity
    nlinarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVAnnulusSelection
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

lemma plane_fderiv_relative_integrable {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : Plane →L[ℝ] ℝ) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ g y-p‖^2) (Metric.ball (0 : Plane) r) :=
  ((((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Plane) r)).mono_set Metric.ball_subset_closedBall

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_mul_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    {ζ f : X → ℝ} {K L A B : ℝ≥0}
    (hζ : LipschitzWith K ζ) (hf : LipschitzWith L f)
    (hA : ∀ x, |ζ x| ≤ A) (hB : ∀ x ∈ Function.support ζ, |f x| ≤ B) :
    LipschitzWith (A * L + B * K) (fun x ↦ ζ x * f x) := by
  have hbound (x y : X) (hy : ζ y ≠ 0) :
      |ζ x * f x - ζ y * f y| ≤ (A * L + B * K : ℝ≥0) * dist x y := by
    have he : ζ x * f x - ζ y * f y = ζ x * (f x - f y) + f y * (ζ x - ζ y) := by ring
    rw [he]
    have h₁ := hf.dist_le_mul x y
    have h₂ := hζ.dist_le_mul x y
    simp only [Real.dist_eq] at h₁ h₂
    calc
      _ ≤ |ζ x| * |f x - f y| + |f y| * |ζ x - ζ y| := by
        simpa only [abs_mul] using abs_add_le (ζ x * (f x - f y)) (f y * (ζ x - ζ y))
      _ ≤ (A : ℝ) * (L * dist x y) + (B : ℝ) * (K * dist x y) :=
        add_le_add (mul_le_mul (hA x) h₁ (abs_nonneg _) (NNReal.coe_nonneg _))
          (mul_le_mul (hB y hy) h₂ (abs_nonneg _) (NNReal.coe_nonneg _))
      _ = _ := by push_cast; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hy : ζ y = 0
  · by_cases hx : ζ x = 0
    · simp only [hx, hy, zero_mul, sub_self, abs_zero]
      positivity
    · simpa only [abs_sub_comm, dist_comm] using hbound y x hx
  · exact hbound x y hy

lemma exists_lipschitz_cutoff_mul {X : Type*} [PseudoMetricSpace X]
    {ζ f : X → ℝ} {K L : ℝ≥0} (hζ : LipschitzWith K ζ) (hf : LipschitzWith L f)
    (hs : HasCompactSupport ζ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x ↦ ζ x * f x) := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuous hζ.continuous
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨A.toNNReal * L + B.toNNReal * K,
    lipschitz_mul_of_bound_on_support hζ hf ?_ ?_⟩
  · intro x
    have hh : |ζ x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hh.trans (le_max_left _ _)
  · intro x hx
    have hh : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (subset_tsupport _ hx)
    exact hh.trans (le_max_left _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma lipschitz_centered_scale_gradient {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a m : ℝ) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y ↦ a * (f y - m)) x‖ ^ 2 =
      a ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  rw [fderiv_const_mul (hx.sub_const m), fderiv_sub_const m, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]

lemma lipschitz_centered_scale_gradient_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a m : ℝ) (S : Set X) :
    (∫ x in S, ‖fderiv ℝ (fun y ↦ a * (f y - m)) x‖ ^ 2 ∂μ) =
      a ^ 2 * ∫ x in S, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_restrict_of_ae (lipschitz_centered_scale_gradient hf a m))

theorem planar_normalized_H1 {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {R e D : ℝ} (hR : 0 < R) (he : 0 < e)
    (henergy : (∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) ≤ D * e ^ 2) :
    let m := (∫ y in planeSquare R, f y) / (2 * R) ^ 2
    let u := fun x ↦ e⁻¹ * (f x - m)
    (∫ x in planeSquare R, ‖fderiv ℝ u x‖ ^ 2) ≤ D ∧
    (∫ x in planeSquare R, u x ^ 2) ≤
      16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 * D := by
  dsimp only
  have hgrad := mul_le_mul_of_nonneg_left henergy (sq_nonneg e⁻¹)
  have heq : e⁻¹ ^ 2 * (D * e ^ 2) = D := by field_simp
  rw [heq] at hgrad
  refine ⟨?_, ?_⟩
  · rw [lipschitz_centered_scale_gradient_integral hf]
    exact hgrad
  · have heq' : (fun x ↦ (e⁻¹ * (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2)) ^ 2) =
        (fun x ↦ e⁻¹ ^ 2 * (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2) ^ 2) := by
      funext x
      exact mul_pow _ _ 2
    rw [heq', integral_const_mul]
    have hp := mul_le_mul_of_nonneg_left (plane_square_poincare hf hR) (sq_nonneg e⁻¹)
    have hC : 0 ≤ 16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 := by
      positivity
    have hb := mul_le_mul_of_nonneg_left hgrad hC
    nlinarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Laplacian
namespace CubicTorus

lemma fderiv_comp_smul_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} {r : ℝ} (hf : DifferentiableAt ℝ f (r • x)) :
    fderiv ℝ (fun y ↦ f (r • y)) x = r • fderiv ℝ f (r • x) := by
  have hh := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  have he : (fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ X) =
      r • fderiv ℝ f (r • x) := by ext y; simp
  simpa only [Function.comp_def, id_eq, he] using hh.fderiv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphRescale_fderiv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : r ≠ 0) (e m : ℝ) (y : Plane) :
    fderiv ℝ (graphRescale r e m f) y = e • fderiv ℝ f (r⁻¹ • y) := by
  have hd : DifferentiableAt ℝ (fun y : Plane ↦ f (r⁻¹ • y)) y :=
    (hf.comp (by fun_prop)).differentiable (by simp) |>.differentiableAt
  unfold graphRescale
  rw [fderiv_const_mul ((hd.const_mul e).const_add m),
    fderiv_const_add m, fderiv_const_mul hd,
    fderiv_comp_smul_eq ((hf.differentiable (by simp)) _), smul_smul,smul_smul]
  congr 1
  field_simp

lemma plane_integral_rescale_ball (f : Plane → ℝ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), f (r⁻¹ • y)) =
      r^2 * ∫ y in Metric.ball (0 : Plane) b, f y := by
  have he (y : Plane) : r⁻¹ • y ∈ Metric.ball (0 : Plane) b ↔
      y ∈ Metric.ball (0 : Plane) (r*b) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    rw [← div_eq_inv_mul,div_lt_iff₀ hr]
    rw [mul_comm b r]
  have hh := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Plane)
    ((Metric.ball (0 : Plane) b).indicator f) hr.le
  have hh' : (fun y : Plane ↦ (Metric.ball (0 : Plane) b).indicator f (r⁻¹ • y)) =
      (Metric.ball (0 : Plane) (r*b)).indicator (fun y ↦ f (r⁻¹ • y)) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Plane) (r*b)
    · rw [indicator_of_mem hy,indicator_of_mem ((he y).mpr hy)]
    · rw [indicator_of_notMem hy,indicator_of_notMem (fun h ↦ hy ((he y).mp h))]
  rw [hh',integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at hh
  simpa only [show Module.finrank ℝ Plane = 2 from finrank_euclideanSpace_fin,smul_eq_mul] using hh

lemma graphRescale_relative_energy {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : 0 < r) (e m b : ℝ) (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ (graphRescale r e m f) y-e • p‖^2) =
      r^2*e^2*(∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ f y-p‖^2) := by
  simp_rw [graphRescale_fderiv hf hr.ne',← smul_sub,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs]
  rw [integral_const_mul,plane_integral_rescale_ball (fun y ↦ ‖fderiv ℝ f y-p‖^2) hr]
  ring

end CubicTorus

end
end

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

theorem exists_sharp_smooth_graph {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ LipschitzWith K g ∧
      (∀ x, |g x-f x| ≤ δ) ∧
      (∀ R : ℝ, (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ g x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2) ∧
      ∀ m e H : ℝ, (∀ y, |m+e*f y| ≤ H) → ∀ y, |m+e*g y| ≤ H := by
  let ρ := δ/((K : ℝ)+1)
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    rw [div_le_iff₀ (by positivity : 0 < (K : ℝ)+1)]
    nlinarith [K.coe_nonneg]
  let b : ContDiffBump (0 : Plane) := ⟨ρ/2,ρ,by positivity,by linarith⟩
  refine ⟨graphSmooth b f,graphSmooth_contDiff b hf,graphSmooth_lipschitz b hf,?_,?_,?_⟩
  · intro x
    apply (graphSmooth_error b hf x).trans
    change (K : ℝ)*ρ ≤ δ
    have hh : ((K : ℝ)+1)*ρ = δ := by dsimp [ρ]; field_simp
    nlinarith
  · intro R
    apply (graphSmooth_local_energy b hf R).2.trans
    exact setIntegral_mono_set (lipschitz_gradient_sq_integrable_ball hf (R+δ))
      (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.ball_subset_ball (add_le_add le_rfl hρδ)).eventuallyLE
  · intro m e H hH y
    exact graphSmooth_affine_abs_le b hf m e H hH y

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma columnPhase_measurable (q : ℝ) : Measurable (columnPhase q) :=
  measurable_const.indicator measurableSet_Iio

lemma columnPhase_difference_le (U : Set Torus) (x : Torus) (q t : ℝ) :
    |characteristic U x-columnPhase q t| ≤ 1 := by
  by_cases hx : x ∈ U <;> by_cases ht : t < q <;>
    simp [characteristic, columnPhase, hx, ht]

lemma columnGraphMismatch_integrable {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (g : Plane → ℝ) (y : Plane) :
    IntegrableOn (fun t ↦ |characteristic U
      (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|)
      (Icc (-r/4) (r/4)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (((measurable_characteristic hU).comp
      (continuous_const.add (continuous_quotientMap.comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable).sub
      (columnPhase_measurable (g y))).abs.aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_abs] using columnPhase_difference_le U _ (g y) t

lemma columnGraphMismatch_nonneg (U : Set Torus) (a : Torus) (n : Cover)
    (r : ℝ) (g : Plane → ℝ) (y : Plane) :
    0 ≤ columnGraphMismatch U a n r g y := integral_nonneg (fun _ ↦ abs_nonneg _)

lemma measurable_columnGraphMismatch {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (columnGraphMismatch U a n r g) := by
  have hc : Continuous (fun p : Plane × ℝ ↦
      a+quotientMap (normalPlaneEmbedding n p.1+p.2 • n)) :=
    continuous_const.add (continuous_quotientMap.comp
      (((normalPlaneLinearIsometry n).continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)))
  have hs : MeasurableSet {p : Plane × ℝ | p.2 < g p.1} :=
    measurableSet_lt measurable_snd (hg.comp measurable_fst)
  have hm : Measurable (fun p : Plane × ℝ ↦ columnPhase (g p.1) p.2) := by
    exact measurable_const.indicator hs
  exact ((((measurable_characteristic hU).comp hc.measurable).sub hm).abs.stronglyMeasurable.integral_prod_right').measurable

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_BVColumnMismatchMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma characteristic_symmDiff_eq_abs (U F : Set Torus) (x : Torus) :
    characteristic (U ∆ F) x = |characteristic U x-characteristic F x| := by
  by_cases hU : x ∈ U <;> by_cases hF : x ∈ F <;>
    simp [characteristic, Set.mem_symmDiff, hU, hF]

lemma graphSublevelIndicator_column (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphSublevelIndicator a n g (normalColumnChart a n (t,y)) = columnPhase (g y) t := by
  simp only [graphSublevelIndicator, graphHeightExtension, Set.indicator,
    Set.mem_ofPred_eq, normalColumnChart_height a hn, normalColumnChart_projection a hn,
    columnPhase, mem_Iio]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma columnPhase_abs_sub (p q t : ℝ) :
    |columnPhase p t-columnPhase q t| =
      (Ico (min p q) (max p q)).indicator (fun _ ↦ (1 : ℝ)) t := by
  by_cases hp : t < p <;> by_cases hq : t < q <;>
    simp only [columnPhase, Set.indicator, mem_Iio, mem_Ico, min_le_iff, lt_max_iff, hp, hq] <;>
      split_ifs <;> simp_all
  first | linarith | (rename_i hbound; rcases hbound with hbound | hbound <;> linarith)

lemma integral_abs_columnPhase_sub (p q : ℝ) :
    Integrable (fun t ↦ |columnPhase p t-columnPhase q t|) ∧
      (∫ t : ℝ, |columnPhase p t-columnPhase q t|) = |p-q| := by
  simp_rw [columnPhase_abs_sub]
  constructor
  · exact (integrableOn_const (ne_of_lt (show volume (Ico (min p q) (max p q)) < ⊤ by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top))).integrable_indicator measurableSet_Ico
  · rw [integral_indicator measurableSet_Ico, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_one]
    simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max)]
    rw [abs_sub_comm]
    exact max_sub_min_eq_abs _ _

lemma columnGraphMismatch_change_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (f g : Plane → ℝ) (y : Plane) :
    columnGraphMismatch U a n r f y ≤ columnGraphMismatch U a n r g y + |f y-g y| := by
  have hp := integral_abs_columnPhase_sub (g y) (f y)
  have hpoint (t : ℝ) : |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (f y) t| ≤
      |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|+
        |columnPhase (g y) t-columnPhase (f y) t| := abs_sub_le _ _ _
  have hi := integral_mono (columnGraphMismatch_integrable hU a n r f y)
    ((columnGraphMismatch_integrable hU a n r g y).add hp.1.integrableOn) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (columnGraphMismatch_integrable hU a n r g y) hp.1.integrableOn] at hi
  have hb : (∫ t in Icc (-r/4) (r/4), |columnPhase (g y) t-columnPhase (f y) t|) ≤ |f y-g y| := by
    rw [abs_sub_comm, ← hp.2]
    exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ ↦ abs_nonneg _) hp.1
  exact hi.trans (add_le_add le_rfl hb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma columnPhase_integral {r q : ℝ} (hq : |q| ≤ r/4) :
    (∫ t in Icc (-r/4) (r/4), columnPhase q t) = q+r/4 := by
  have hset : Icc (-r/4) (r/4) ∩ Iio q = Ico (-r/4) q := by
    ext t
    simp only [mem_inter_iff,mem_Icc,mem_Iio,mem_Ico]
    constructor
    · exact fun h ↦ ⟨h.1.1,h.2⟩
    · exact fun h ↦ ⟨⟨h.1,h.2.le.trans (abs_le.mp hq).2⟩,h.2⟩
  unfold columnPhase
  rw [setIntegral_indicator measurableSet_Iio,hset,integral_const,smul_eq_mul,mul_one,
    measureReal_def,Measure.restrict_apply_univ,Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith [(abs_le.mp hq).1] : 0 ≤ q- -r/4)]
  ring

lemma normalColumnHeight_error_le_mismatch {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) {g : Plane → ℝ} (y : Plane) (hg : |g y| ≤ r/4) :
    |g y-normalColumnHeight U a n r y| ≤ columnGraphMismatch U a n r g y := by
  have hi : IntegrableOn (columnPhase (g y)) (Icc (-r/4) (r/4)) :=
    (integrable_const (1:ℝ)).indicator measurableSet_Iio
  have heq : columnGraphMismatch U a n r g y = ∫ t in Icc (-r/4) (r/4),
      |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t| := rfl
  rw [abs_sub_comm,normalColumnHeight]
  have he : (∫ t in Icc (-r/4) (r/4), characteristic U
      (a+quotientMap (normalPlaneEmbedding n y+t • n))) -r/4-g y =
      ∫ t in Icc (-r/4) (r/4), (characteristic U
        (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t) := by
    rw [integral_sub (normalColumn_integrable hU a n r y) hi,columnPhase_integral hg]
    ring
  rw [he,heq]
  exact abs_integral_le_integral_abs

lemma columnGraphMismatch_bound {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) (g : Plane → ℝ) (y : Plane) :
    columnGraphMismatch U a n r g y ≤ r/2 := by
  have hh := integral_mono (columnGraphMismatch_integrable hU a n r g y)
    (integrable_const (1:ℝ)) (fun t ↦ columnPhase_difference_le U _ (g y) t)
  rw [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,
    Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ r/4- -r/4)] at hh
  exact hh.trans_eq (by ring)

lemma columnGraphMismatch_integrable_ball {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {g : Plane → ℝ} (hg : Measurable g)
    (R : ℝ) : IntegrableOn (columnGraphMismatch U a n r g) (Metric.ball 0 R) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply (integrable_const (r/2)).mono'
  · exact (measurable_columnGraphMismatch hU a n r hg).aestronglyMeasurable
  · exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (columnGraphMismatch_nonneg _ _ _ _ _ _)]
      exact columnGraphMismatch_bound hU a n hr g y

lemma columnGraphMismatch_integral_change_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {f g : Plane → ℝ}
    (hf : Measurable f) (hg : Measurable g) {δ : ℝ} (he : ∀ y, |f y-g y| ≤ δ) (R : ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r f y) ≤
      (∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r g y) +
        δ*(volume : Measure Plane).real (Metric.ball 0 R) := by
  have hfin : (volume : Measure Plane) (Metric.ball 0 R) ≠ ⊤ := measure_ball_lt_top.ne
  have hi := integral_mono (columnGraphMismatch_integrable_ball hU a n hr hf R)
    ((columnGraphMismatch_integrable_ball hU a n hr hg R).add (integrableOn_const hfin))
    (fun y ↦ (columnGraphMismatch_change_le hU a n r f g y).trans (add_le_add le_rfl (he y)))
  simp only [Pi.add_apply] at hi
  rw [integral_add (columnGraphMismatch_integrable_ball hU a n hr hg R)
    (integrableOn_const hfin),setIntegral_const] at hi
  simpa only [smul_eq_mul,mul_comm] using hi

lemma normalColumnHeight_integral_error_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {g : Plane → ℝ}
    (hg : Measurable g) (hb : ∀ y, |g y| ≤ r/4) (R : ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, |g y-normalColumnHeight U a n r y|) ≤
      ∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r g y := by
  have hi := columnGraphMismatch_integrable_ball hU a n hr hg R
  have hb' := fun y ↦ normalColumnHeight_error_le_mismatch hU a n r y (hb y)
  have hi' : IntegrableOn (fun y ↦ |g y-normalColumnHeight U a n r y|) (Metric.ball 0 R) := by
    apply hi.mono'
    · exact (hg.sub (measurable_normalColumnHeight hU a n r)).abs.aestronglyMeasurable
    · exact Eventually.of_forall fun y ↦ by simpa only [Real.norm_eq_abs,abs_abs] using hb' y
  exact integral_mono hi' hi hb'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma plane_ball_real_volume_scale {r : ℝ} (hr : 0 < r) (b : ℝ) :
    (volume : Measure Plane).real (Metric.ball 0 (r*b)) =
      r^2*(volume : Measure Plane).real (Metric.ball 0 b) := by
  have hh := plane_integral_rescale_ball (fun _ ↦ (1:ℝ)) hr b
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphNormalize_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (r e m : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (graphNormalize r e m g) := by
  exact contDiff_const.mul ((hg.comp (by fun_prop)).sub contDiff_const)

lemma graphRescale_normalize {r e : ℝ} (hr : r ≠ 0) (he : e ≠ 0)
    (m : ℝ) (g : Plane → ℝ) : graphRescale r e m (graphNormalize r e m g) = g := by
  funext y
  simp only [graphRescale,graphNormalize,smul_smul,mul_inv_cancel₀ hr,one_smul]
  field_simp
  ring

lemma graphNormalize_lipschitz {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {r e : ℝ} (hr : 0 < r) (he : 0 < e) (m : ℝ) :
    LipschitzWith (⟨e⁻¹,inv_nonneg.mpr he.le⟩*K) (graphNormalize r e m g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hg.dist_le_mul (r • x) (r • y)
  rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hr,Real.dist_eq] at hh
  have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_nonneg hr.le he.le))
  have hdiff : graphNormalize r e m g x-graphNormalize r e m g y =
      (r*e)⁻¹*(g (r • x)-g (r • y)) := by unfold graphNormalize; ring
  rw [Real.dist_eq,hdiff,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos hr he))]
  apply ht.trans_eq
  change (r*e)⁻¹*((K:ℝ)*(r*dist x y)) = (e⁻¹*(K:ℝ))*dist x y
  field_simp

lemma graphNormalize_energy {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {r e : ℝ} (hr : 0 < r) (he : 0 < e) (m b : ℝ) :
    r^2*e^2*(∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphNormalize r e m g) y‖^2) =
      ∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ g y‖^2 := by
  have hh := graphRescale_relative_energy (graphNormalize_contDiff hg r e m) hr e m b
    (0 : Plane →L[ℝ] ℝ)
  simpa only [graphRescale_normalize hr.ne' he.ne',smul_zero,sub_zero] using hh.symm

lemma graphNormalize_height {r e α : ℝ} (hr : 0 < r) (he : e ≠ 0)
    (m : ℝ) {g : Plane → ℝ} (hg : ∀ y, |g y| ≤ α*r) (y : Plane) :
    |m+e*graphNormalize r e m g y| ≤ α := by
  have heq : m+e*graphNormalize r e m g y = r⁻¹*g (r • y) := by
    unfold graphNormalize
    field_simp
    ring
  rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hr)]
  apply (mul_le_mul_of_nonneg_left (hg _) (inv_nonneg.mpr hr.le)).trans_eq
  field_simp

lemma planeSquare_subset_closedBall {R : ℝ} (_hR : 0 ≤ R) :
    planeSquare R ⊆ Metric.closedBall 0 (‖planeProductCoordinates.symm.toContinuousLinearMap‖*R) := by
  intro x hx
  have hb : ‖planeProductCoordinates x‖ ≤ R := by
    rw [Prod.norm_def]
    exact max_le (abs_le.mpr hx.1) (abs_le.mpr hx.2)
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh := planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (planeProductCoordinates x)
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using
    hh.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

lemma ball_subset_planeSquare {R ρ : ℝ} (_hR : 0 ≤ R)
    (hρ : ‖planeProductCoordinates.toContinuousLinearMap‖*ρ ≤ R) :
    Metric.ball (0 : Plane) ρ ⊆ planeSquare R := by
  intro x hx
  have hh := planeProductCoordinates.toContinuousLinearMap.le_opNorm x
  have hn : ‖x‖ ≤ ρ := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < ρ).le
  have hb := hh.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans hρ)
  change ‖planeProductCoordinates x‖ ≤ R at hb
  rw [Prod.norm_def] at hb
  exact ⟨abs_le.mp (le_max_left _ _ |>.trans hb),abs_le.mp (le_max_right _ _ |>.trans hb)⟩

lemma planeSquare_mean_abs_le {f : Plane → ℝ} (hf : Continuous f)
    {R α : ℝ} (hR : 0 < R) (hα : ∀ y, |f y| ≤ α) :
    |(∫ y in planeSquare R, f y)/(2*R)^2| ≤ α := by
  have hi : IntegrableOn f (planeSquare R) := hf.continuousOn.integrableOn_compact (isCompact_planeSquare R)
  have hfin : (volume : Measure Plane) (planeSquare R) ≠ ⊤ := (isCompact_planeSquare R).measure_lt_top.ne
  have hb : |∫ y in planeSquare R, f y| ≤ α*(2*R)^2 := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _y in planeSquare R, α := integral_mono hi.norm (integrableOn_const hfin) hα
      _ = _ := by rw [setIntegral_const,planeSquare_volume R hR.le]; simp only [smul_eq_mul]; ring
  rw [abs_div,abs_of_pos (by positivity : 0 < (2*R)^2),div_le_iff₀ (by positivity)]
  exact hb

theorem smooth_graph_normalized_H1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgLip : LipschitzWith K g)
    {r e R b α D : ℝ} (hr : 0 < r) (he : 0 < e) (hR : 0 < R)
    (hs : planeSquare R ⊆ Metric.ball (0 : Plane) b)
    (hh : ∀ y, |g y| ≤ α*r)
    (henergy : (∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ g y‖^2) ≤ r^2*e^2*D) :
    ∃ m : ℝ, |m| ≤ α ∧
      (∫ y in planeSquare R, ‖fderiv ℝ (graphNormalize r e m g) y‖^2) ≤ D ∧
      (∫ y in planeSquare R, (graphNormalize r e m g y)^2) ≤
        16*R^2*‖planeProductCoordinates.symm.toContinuousLinearMap‖^2*D := by
  let g₀ := graphNormalize r 1 0 g
  have hL : LipschitzWith K g₀ := by
    have h := graphNormalize_lipschitz hgLip hr (by norm_num : (0:ℝ)<1) 0
    exact h.weaken (by change (1:ℝ)⁻¹*(K:ℝ) ≤ K; simp)
  have hc : Continuous g₀ := (graphNormalize_contDiff hg r 1 0).continuous
  have hgb : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ g₀ y‖^2) ≤ D*e^2 := by
    have heq := graphNormalize_energy hg hr (by norm_num : (0:ℝ)<1) 0 b
    dsimp only [g₀] at ⊢
    simp only [one_pow,mul_one] at heq
    have htt := heq.le.trans henergy
    nlinarith [sq_pos_of_pos hr]
  have hgs : (∫ y in planeSquare R, ‖fderiv ℝ g₀ y‖^2) ≤ D*e^2 := by
    exact (setIntegral_mono_set (lipschitz_gradient_sq_integrable_ball hL b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) hs.eventuallyLE).trans hgb
  let m := (∫ y in planeSquare R, g₀ y)/(2*R)^2
  refine ⟨m,?_,?_⟩
  · apply planeSquare_mean_abs_le hc hR
    intro y
    simpa only [zero_add,one_mul] using graphNormalize_height hr one_ne_zero 0 hh y
  · have heq : (fun y ↦ e⁻¹*(g₀ y-m)) = graphNormalize r e m g := by
      funext y
      dsimp only [g₀,graphNormalize]
      field_simp
      ring
    have hp := planar_normalized_H1 hL hR he hgs
    change (∫ y in planeSquare R, ‖fderiv ℝ (fun x ↦ e⁻¹*(g₀ x-m)) y‖^2) ≤ D ∧
      (∫ y in planeSquare R, (e⁻¹*(g₀ y-m))^2) ≤ _ at hp
    rw [← heq]
    exact hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem local_planar_H1_strong_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {S : Set Plane} (hS : IsCompact S) (hball : Metric.ball (0 : Plane) (4 * R) ⊆ S)
    {ζ : Plane → ℝ} {Lζ : ℝ≥0} (hζ : ContDiff ℝ 1 ζ)
    (hζLip : LipschitzWith Lζ ζ) (hζs : tsupport ζ ⊆ S)
    (hζone : ∀ x ∈ Metric.ball (0 : Plane) (4 * R), ζ x = 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, |ζ x| ≤ A) (hb : ∀ x, ‖fderiv ℝ ζ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x in S, f i x ^ 2) ≤ M) →
        (∀ i, (∫ x in S, ‖fderiv ℝ (f i) x‖ ^ 2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4 * R) →
          Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (v : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ v x-fderiv ℝ v 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨C₀, hC₀, happ⟩ := planar_H1_strong_harmonic_approximation hR hS hball
  refine ⟨C₀ * (A ^ 2 + 1), by positivity, ?_⟩
  intro f L hf M D hD hM hgrad hw
  have hMnon : 0 ≤ M := (integral_nonneg (fun x ↦ sq_nonneg (f 0 x))).trans (hM 0)
  have hs : HasCompactSupport ζ := hS.of_isClosed_subset isClosed_closure hζs
  let u : ℕ → Plane → ℝ := fun i x ↦ ζ x * f i x
  have huLip (i : ℕ) := exists_lipschitz_cutoff_mul hζLip (hf i) hs
  choose K hK using huLip
  have henergy (i : ℕ) := lipschitz_cutoff_H1 (μ := volume) (hf i) hζ hs hS hζs hA hB ha hb
  have hglobalM (i : ℕ) : (∫ x, u i x ^ 2) ≤ A ^ 2 * M :=
    (henergy i).2.2.1.trans (mul_le_mul_of_nonneg_left (hM i) (sq_nonneg A))
  have hglobalD (i : ℕ) : (∫ x, ‖fderiv ℝ (u i) x‖ ^ 2) ≤
      2 * A ^ 2 * D + 2 * B ^ 2 * M := by
    exact (henergy i).2.2.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hgrad i) (by positivity))
      (mul_le_mul_of_nonneg_left (hM i) (by positivity)))
  have hw' (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : HasCompactSupport φ)
      (hφb : tsupport φ ⊆ Metric.ball 0 (4 * R)) :
      Tendsto (fun i ↦ ∫ y, u i y * Δ φ y) atTop (𝓝 0) := by
    have he (i : ℕ) : (fun y ↦ u i y * Δ φ y) = (fun y ↦ f i y * Δ φ y) := by
      funext y
      by_cases hy : y ∈ tsupport φ
      · simp only [u, hζone y (hφb hy), one_mul]
      · have hz : Δ φ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh ↦ hy (laplacian_tsupport_subset hφ hh))
        simp only [hz, mul_zero]
    simpa only [he] using hw φ hφ hφs hφb
  obtain ⟨ψ, v, hψ, hv, he, hdec⟩ := happ u K hK (fun i ↦ (henergy i).1)
    (fun i ↦ (henergy i).2.1) (A ^ 2 * M) (2 * A ^ 2 * D + 2 * B ^ 2 * M)
    (by positivity) hglobalM hglobalD hw'
  refine ⟨ψ,v,hψ,hv,?_,?_⟩
  · have heq (i : ℕ) : (∫ x in Metric.ball (0 : Plane) R, (u (ψ i) x-v x)^2) =
        ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      have hx' := (Metric.ball_subset_ball (by linarith : R ≤ 4*R)) hx
      simp only [u,hζone x hx',one_mul]
    simpa only [heq] using he
  · intro ρ hρ
    apply (hdec ρ hρ).trans
    have ht : A^2*M ≤ (A^2+1)*M := by nlinarith
    have ht' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC₀.le)
      (pow_nonneg hρ 4)
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma exists_planeSquare_cutoff {Q : ℝ} (hQ : 0 < Q) :
    ∃ R : ℝ, ∃ ζ : Plane → ℝ, ∃ L : ℝ≥0, 0 < R ∧
      Metric.ball (0 : Plane) (4*R) ⊆ planeSquare Q ∧
      ContDiff ℝ 1 ζ ∧ LipschitzWith L ζ ∧ tsupport ζ ⊆ planeSquare Q ∧
      (∀ x ∈ Metric.ball (0 : Plane) (4*R), ζ x = 1) ∧
      (∀ x, |ζ x| ≤ 1) ∧ (∀ x, ‖fderiv ℝ ζ x‖ ≤ (L:ℝ)) := by
  let ρ := Q/(‖planeProductCoordinates.toContinuousLinearMap‖+1)
  have hρ : 0 < ρ := div_pos hQ (by positivity)
  have hh : ‖planeProductCoordinates.toContinuousLinearMap‖*ρ ≤ Q := by
    dsimp [ρ]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0 < ‖planeProductCoordinates.toContinuousLinearMap‖+1)]
    nlinarith
  have hb := ball_subset_planeSquare hQ.le hh
  let b : ContDiffBump (0 : Plane) := ⟨ρ/4,ρ/2,by positivity,by linarith⟩
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    (b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b) (by simp)
  refine ⟨ρ/16,b,L,by positivity,?_,(b.contDiff : ContDiff ℝ 1 b),hL,?_,?_,?_,?_⟩
  · apply (Metric.ball_subset_ball (by linarith : 4*(ρ/16) ≤ ρ)).trans hb
  · rw [b.tsupport_eq]
    apply (Metric.closedBall_subset_ball (by change ρ/2 < ρ; linarith)).trans hb
  · intro x hx
    apply b.one_of_mem_closedBall
    exact Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by change 4*(ρ/16) ≤ ρ/4; linarith)) hx)
  · intro x
    rw [abs_of_nonneg (b.nonneg)]
    exact b.le_one
  · intro x
    exact norm_fderiv_le_of_lipschitz ℝ hL

theorem planeSquare_H1_strong_harmonic {Q : ℝ} (hQ : 0 < Q) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ Metric.ball (0 : Plane) (4*R) ⊆ planeSquare Q ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x in planeSquare Q, f i x^2) ≤ M) →
        (∀ i, (∫ x in planeSquare Q, ‖fderiv ℝ (f i) x‖^2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4*R) →
          Tendsto (fun i ↦ ∫ y, f i y*Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (v : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ v x-fderiv ℝ v 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨R,ζ,L,hR,hball,hζ,hL,hs,hone,ha,hb⟩ := exists_planeSquare_cutoff hQ
  obtain ⟨C,hC,happ⟩ := local_planar_H1_strong_harmonic_approximation hR (isCompact_planeSquare Q)
    hball hζ hL hs hone (by norm_num : (0:ℝ)≤1) L.coe_nonneg ha hb
  exact ⟨R,C,hR,hC,hball,happ⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus

lemma exists_small_planeSquare : ∃ Q : ℝ, 0 < Q ∧
    planeSquare Q ⊆ Metric.ball (0 : Plane) (1/8) := by
  let K := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let Q := 1/(16*(K+1))
  have hK : 0 ≤ K := norm_nonneg _
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q,hQ,(planeSquare_subset_closedBall hQ.le).trans (Metric.closedBall_subset_ball ?_)⟩
  change K*Q < 1/8
  dsimp [Q]
  rw [← mul_div_assoc,div_lt_iff₀ (by positivity : 0 < 16*(K+1))]
  linarith

lemma strongL2_restrict_ball {f : ℕ → Plane → ℝ} {u : Plane → ℝ}
    (hf : ∀ i, Continuous (f i)) (hu : Continuous u) {R S : ℝ} (hRS : R ≤ S)
    (hlim : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) S, (f i y-u y)^2) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) R, (f i y-u y)^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun y ↦ sq_nonneg _) _ hlim
  apply Eventually.of_forall
  intro i
  exact setIntegral_mono_set
    (((hf i |>.sub hu).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) S) |>.mono_set
      Metric.ball_subset_closedBall) (Eventually.of_forall fun y ↦ sq_nonneg _)
    (Metric.ball_subset_ball hRS).eventuallyLE

lemma directionalFlux_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (i : Fin 3) (g : Cover → ℝ) : directionalFlux E i g = directionalFlux F i g := by
  exact setIntegral_congr_set (liftSet_congr_ae h)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma norm_sub_sq_le_two {X : Type*} [NormedAddCommGroup X] (a b : X) :
    ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have hh := norm_sub_le a b
  have hn := norm_nonneg (a-b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

lemma graph_relative_energy_bound {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Q R D : ℝ} (hs : Metric.ball (0 : Plane) R ⊆ planeSquare Q)
    (hD : (∫ y in planeSquare Q, ‖fderiv ℝ f y‖^2) ≤ D) (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y-p‖^2) ≤
      2*D+2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 R) := by
  have hc := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hi : IntegrableOn (fun y ↦ ‖fderiv ℝ f y‖^2) (planeSquare Q) :=
    (hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_planeSquare Q)
  have hrel := plane_fderiv_relative_integrable hf p R
  have hb : (∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y‖^2) ≤ D :=
    (setIntegral_mono_set hi (Eventually.of_forall fun y ↦ sq_nonneg _) hs.eventuallyLE).trans hD
  have hfin : (volume : Measure Plane) (Metric.ball 0 R) ≠ ⊤ := measure_ball_lt_top.ne
  calc
    _ ≤ ∫ y in Metric.ball (0 : Plane) R, 2*‖fderiv ℝ f y‖^2+2*‖p‖^2 :=
      integral_mono hrel (((hi.mono_set hs).const_mul 2).add (integrableOn_const hfin))
        (fun y ↦ norm_sub_sq_le_two _ _)
    _ = 2*(∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y‖^2)+
        2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 R) := by
      rw [integral_add ((hi.mono_set hs).const_mul 2) (integrableOn_const hfin),integral_const_mul,
        setIntegral_const,smul_eq_mul]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) le_rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
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
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 3 / 8) :
    Metric.ball (c : Cover) r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - (c : Cover)‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans_lt hx'
  change ‖x i - (c : Cover) i‖ < r at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma radialCore_compactSupport : HasCompactSupport (radialCore c) :=
  (radialBump c).hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport (radialCore c) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport ((radialBump c) : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [(radialBump c).tsupport_eq] at hs
  have hnorm : ‖x - (c : Cover)‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans hnorm
  change ‖x i - (c : Cover) i‖ ≤ 1 / 3 at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    (radialSquared c) x = 1 - (radialBump c) x * (1 - ‖x - (c : Cover)‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    (radialSquared c) x < t ↔ ‖x - (c : Cover)‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - (c : Cover))
  have hb0 : 0 ≤ (radialBump c) x := (radialBump c).nonneg
  have hb1 : (radialBump c) x ≤ 1 := (radialBump c).le_one
  have he (h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16) : (radialBump c) x = 1 := by
    apply (radialBump c).one_of_mem_closedBall
    change dist x (c : Cover) ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - (c : Cover)‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion (radialSquared c) (r ^ 2) = (cubeBall c) r := by
  ext z
  change (radialSquared c) (representative z) < r ^ 2 ↔
    dist (representative z) (c : Cover) < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma cubeBall_eq_metricBall {r : ℝ} (hr : r ≤ 3/8) :
    cubeBall c r = Metric.ball (quotientMap c) r := by
  change representative ⁻¹' Metric.ball (c : Cover) r = _
  rw [← image_quotientMap_eq_preimage_representative (coverBall_subset_cube hr)]
  have he : Metric.ball (c : Cover) r = (fun v : Cover ↦ v+(c : Cover)) '' Metric.ball 0 r := by
    ext x
    constructor
    · intro hx
      exact ⟨x-c, by simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx, sub_add_cancel _ _⟩
    · rintro ⟨v,hv,rfl⟩
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hv
  rw [he, image_image]
  simp_rw [quotientMap_add]
  exact quotientMap_chart_image_ball _ (by linarith)

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma center_add_mem {x : Cover} (hx : ‖x‖ < 3/8) :
    (c : Cover)+x ∈ fundamentalCube := by
  intro i
  have hi := (PiLp.norm_apply_le x i).trans_lt hx
  rw [Real.norm_eq_abs, abs_lt] at hi
  change 0 ≤ (c : Cover) i+x i ∧ (c : Cover) i+x i < 1
  have hc := coords c i
  constructor <;> linarith

lemma torusGraphRegion_symmDiff_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume ((U ∆ torusGraphRegion (c : Cover) n g) ∩
      Metric.ball (quotientMap (c : Cover)) s) ≤
      ∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap (c : Cover)) n r g y) := by
  let D := U ∆ torusGraphRegion (c : Cover) n g
  have hD : MeasurableSet D := hU.symmDiff (measurableSet_torusGraphRegion _ _ hg)
  let f : Cover → ℝ≥0∞ := (Metric.ball (0 : Cover) s).indicator
    (fun x ↦ ENNReal.ofReal (characteristic D (quotientMap x+quotientMap (c : Cover))))
  have hf : Measurable f := (((measurable_characteristic hD).comp
    (measurable_quotientMap.add_const _)).ennreal_ofReal).indicator measurableSet_ball
  have he : torusVolume (D ∩ Metric.ball (quotientMap (c : Cover)) s) = ∫⁻ x, f x := by
    have hm := lintegral_map (μ := volume.restrict (Metric.ball (0 : Cover) s))
      ((measurable_characteristic hD).ennreal_ofReal) (measurable_quotientMap.add_const (quotientMap (c : Cover)))
    rw [torusVolume_chart_map_restrict _ (by linarith : s ≤ 1/2)] at hm
    rw [lintegral_indicator measurableSet_ball]
    rw [← hm]
    have hi : (fun x ↦ ENNReal.ofReal (characteristic D x)) = D.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [characteristic, hx]
    rw [hi, lintegral_indicator hD, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hD]
  rw [he, ← (normalColumnChart_measurePreserving 0 n).lintegral_comp hf]
  have hb (t : ℝ) (y : Plane) : f (normalColumnChart 0 n (t,y)) ≤
      (Metric.ball (0 : Plane) (r/4)).indicator (fun y ↦ (Icc (-r/4) (r/4)).indicator
        (fun t ↦ ENNReal.ofReal |characteristic U
          (quotientMap (c : Cover)+quotientMap (normalPlaneEmbedding n y+t • n))-
            columnPhase (g y) t|) t) y := by
    let x := normalColumnChart (0 : Cover) n (t,y)
    by_cases hx : x ∈ Metric.ball (0 : Cover) s
    · have hxnorm : ‖x‖ < s := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      have ht : |t| ≤ ‖x‖ := by
        have hh := abs_real_inner_le_norm n x
        rw [hn, one_mul] at hh
        have ht0 : ⟪n,x⟫ = t := by simpa only [x, sub_zero] using normalColumnChart_height 0 hn t y
        rwa [ht0] at hh
      have hy : ‖y‖ ≤ ‖x‖ := by
        have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0
        have hy0 : normalPlaneCoordinates n x = y := by
          simpa only [x, sub_zero] using normalColumnChart_projection 0 hn t y
        simpa only [map_zero, hy0, dist_zero_right, one_mul, NNReal.coe_one] using hh
      rw [indicator_of_mem (show y ∈ Metric.ball (0 : Plane) (r/4) by
        simpa only [Metric.mem_ball, dist_zero_right] using hy.trans_lt (hxnorm.trans_le hs))]
      rw [indicator_of_mem (show t ∈ Icc (-r/4) (r/4) by
        have hh := abs_le.mp (ht.trans (hxnorm.le.trans hs)); constructor <;> linarith)]
      dsimp [f]
      rw [indicator_of_mem hx, characteristic_symmDiff_eq_abs]
      have hxc : (c : Cover)+x ∈ fundamentalCube := center_add_mem (by linarith)
      have heq : quotientMap x+quotientMap (c : Cover) = quotientMap ((c : Cover)+x) := by
        rw [quotientMap_add, add_comm]
      rw [heq, characteristic_torusGraphRegion hxc]
      have hc : (c : Cover)+x = normalColumnChart (c : Cover) n (t,y) := by
        simp only [x, normalColumnChart_apply _ hn, zero_add]
      rw [hc, graphSublevelIndicator_column _ hn]
      rw [normalColumnChart_apply _ hn, quotientMap_add]
    · change f x ≤ _
      dsimp [f]
      rw [indicator_of_notMem hx]
      exact zero_le
  calc
    _ ≤ ∫⁻ y : Plane, ∫⁻ t : ℝ, (Metric.ball (0 : Plane) (r/4)).indicator
        (fun y ↦ (Icc (-r/4) (r/4)).indicator
          (fun t ↦ ENNReal.ofReal |characteristic U
            (quotientMap (c : Cover)+quotientMap (normalPlaneEmbedding n y+t • n))-
              columnPhase (g y) t|) t) y := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod_symm (fun p : ℝ × Plane ↦ f (normalColumnChart 0 n p))
        (hf.comp (normalColumnChart 0 n).measurable).aemeasurable]
      exact lintegral_mono fun y ↦ lintegral_mono fun t ↦ hb t y
    _ = _ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Metric.ball (0 : Plane) (r/4)
      · simp only [indicator_of_mem hy]
        rw [lintegral_indicator measurableSet_Icc]
        exact (ofReal_integral_eq_lintegral_ofReal (columnGraphMismatch_integrable hU _ n r g y)
          (Eventually.of_forall fun _ ↦ abs_nonneg _)).symm
      · simp only [indicator_of_notMem hy, lintegral_zero]

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVMovingOrientedReplacement
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma torusGraphRegion_symmDiff_real_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume.real ((U ∆ torusGraphRegion (c : Cover) n g) ∩ Metric.ball (quotientMap (c : Cover)) s) ≤
      ∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U (quotientMap (c : Cover)) n r g y := by
  have hh := torusGraphRegion_symmDiff_ball_le (c:=c) hU hn hrs hs hg
  rw [← ofReal_integral_eq_lintegral_ofReal
    (columnGraphMismatch_integrable_ball hU _ n hr hg.measurable (r/4))
    (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hh
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at ht
  exact ht

theorem exists_physical_smooth_graph {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {r δ α : ℝ} (hr : 0 < r) (hrs : r < 1) (hδ : 0 < δ) (hδr : δ ≤ r/8)
    (hα : α ≤ 1/4) (hheight : ∀ y, |g y| ≤ α*r) :
    ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith K G ∧
      (∀ y, |G y| ≤ α*r) ∧
      (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ∧
      (let B := (∫ y in Metric.ball (0 : Plane) (r/4),
          columnGraphMismatch U (quotientMap (c : Cover)) n r g y)+
            δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4))
       (∫ y in Metric.ball (0 : Plane) (r/4),
          |G y-normalColumnHeight U (quotientMap (c : Cover)) n r y|) ≤ B ∧
       ∀ s : ℝ, s ≤ r/4 → torusVolume.real ((U ∆ torusGraphRegion (c : Cover) n G) ∩
         Metric.ball (quotientMap (c : Cover)) s) ≤ B) := by
  obtain ⟨G,hG,hGL,he,henergy,hH⟩ := exists_sharp_smooth_graph hg hδ
  have hh (y : Plane) : |G y| ≤ α*r := by
    simpa only [zero_add,one_mul] using hH 0 1 (α*r) (by simpa only [zero_add,one_mul] using hheight) y
  have hb (y : Plane) : |G y| ≤ r/4 := (hh y).trans (by nlinarith)
  refine ⟨G,hG,hGL,hh,?_,?_⟩
  · exact (henergy (r/8)).trans (setIntegral_mono_set
      (lipschitz_gradient_sq_integrable_ball hg (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball (by linarith)).eventuallyLE)
  · have herr := columnGraphMismatch_integral_change_le hU (quotientMap (c : Cover)) n hr.le
      hG.continuous.measurable hg.continuous.measurable he (r/4)
    have hv : (volume : Measure Plane).real (Metric.ball 0 (r/4)) =
        r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_one_div] using plane_ball_real_volume_scale hr (1/4)
    rw [hv] at herr
    have herr' : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
        (quotientMap (c : Cover)) n r G y) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
          (quotientMap (c : Cover)) n r g y)+δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_assoc] using herr
    exact ⟨(normalColumnHeight_integral_error_le hU _ n hr.le hG.continuous.measurable hb (r/4)).trans herr',
      fun s hs ↦ (torusGraphRegion_symmDiff_real_ball_le hU hn hr.le hrs hs hG.continuous).trans herr'⟩

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_smooth_trapped_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ D : ℝ, 0 < r₀ ∧ 0 ≤ D ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 → ∀ r α e : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1/4 →
        0 < e → e ≤ 1/2 →
        (normalCap (quotientMap (c : Cover)) n r (α*r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c : Cover)) (-n) r (α*r) ⊆ openRepresentative E) →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith 1 G ∧
        (∀ y, |G y| ≤ α*r) ∧
        (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤ r^2*e^2*D ∧
        (let B := r^3*e^2*(D*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4)))
         (∫ y in Metric.ball (0 : Plane) (r/4),
            |G y-normalColumnHeight (openRepresentative E) (quotientMap (c : Cover)) n r y|) ≤ B ∧
         ∀ s : ℝ, s ≤ r/4 → torusVolume.real
           (((openRepresentative E) ∆ torusGraphRegion (c : Cover) n G) ∩
             Metric.ball (quotientMap (c : Cover)) s) ≤ B) := by
  obtain ⟨R,C,hR,hC,happ⟩ := isMinimizerAt_tightly_trapped_graph_approximation
    hV hE hmin (by norm_num : (0:ℝ)<1/2) le_rfl
  refine ⟨min R (1/4),C.toReal,by positivity,ENNReal.toReal_nonneg,?_⟩
  intro μ hμ N hN hp hunit c n hn r α e hr hrr hα0 hα he hes htrap htilt
  have hrs : r < 1 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S,g,hg,hh,hS,hgood,hcone,hbad,henergy,hmismatch⟩ :=
    happ μ hμ N hN hp hunit (quotientMap (c : Cover)) n hn r α hr
      (hrr.trans (min_le_left _ _)) hα0 hα htrap
  have hg1 : LipschitzWith 1 g := hg.weaken (by
    change (2:ℝ)*(1/2) ≤ 1
    norm_num)
  let T := ∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
    ∂(spatialNormalMeasure μ : Measure Torus)
  have hT : 0 ≤ T := integral_nonneg fun x ↦ sq_nonneg _
  have hgE : (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ≤ C.toReal*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal (lipschitz_gradient_sq_integrable_ball hg1 (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _)] at henergy
    have ht := ENNReal.toReal_mono (by finiteness) henergy
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun y ↦ sq_nonneg _)] using ht
  have hgM : (∫ y in Metric.ball (0 : Plane) (r/4),
      columnGraphMismatch (openRepresentative E) (quotientMap (c : Cover)) n r g y) ≤
        C.toReal*α*r*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (columnGraphMismatch_integrable_ball (isOpen_openRepresentative E).measurableSet
        _ n hr.le hg1.continuous.measurable (r/4))
      (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hmismatch
    have ht := ENNReal.toReal_mono (by finiteness) hmismatch
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun x ↦ sq_nonneg _),ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofReal
        (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] using ht
  have hδ : 0 < r*e^3 := by positivity
  have he3 : e^3 ≤ 1/8 := by nlinarith [mul_le_mul_of_nonneg_left hes he.le, sq_nonneg (e-1/2)]
  have hδr : r*e^3 ≤ r/8 := by nlinarith
  obtain ⟨G,hG,hGL,hheight,hGE,hGM⟩ := exists_physical_smooth_graph (c:=c)
    (isOpen_openRepresentative E).measurableSet hn hg1 hr hrs hδ hδr hα.le hh
  have hB : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch
      (openRepresentative E) (quotientMap (c : Cover)) n r g y)+
      (r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) ≤
      r^3*e^2*(C.toReal*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4))) := by
    have hx := hgM.trans (mul_le_mul_of_nonneg_left htilt (by positivity : 0 ≤ C.toReal*α*r))
    calc
      _ ≤ C.toReal*α*r*(r^2*e^2)+(r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := add_le_add hx le_rfl
      _ = _ := by ring
  refine ⟨G,hG,hGL,hheight,?_,hGM.1.trans hB,fun s hs ↦ (hGM.2 s hs).trans hB⟩
  exact hGE.trans (hgE.trans ((mul_le_mul_of_nonneg_left htilt ENNReal.toReal_nonneg).trans_eq (by ring)))

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapped_harmonic_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ Q R D M C : ℝ, 0 < r₀ ∧ 0 < Q ∧ 0 < R ∧ R ≤ 1/8 ∧
      0 ≤ D ∧ 0 ≤ M ∧ 0 < C ∧ Metric.ball (0 : Plane) R ⊆ planeSquare Q ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (m : ℕ → ℝ) (g : ℕ → Plane → ℝ) (ψ : ℕ → ℕ) (u : Plane → ℝ),
        StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) ∧ LipschitzWith 1 (g i) ∧
          (∀ y, |g i y| ≤ α i*r i) ∧ |m i| ≤ α i ∧
          (∫ y in planeSquare Q, ‖fderiv ℝ (graphNormalize (r i) (e i) (m i) (g i)) y‖^2) ≤ D ∧
          (∫ y in planeSquare Q, (graphNormalize (r i) (e i) (m i) (g i) y)^2) ≤ M ∧
          (∀ s : ℝ, s ≤ r i/4 → torusVolume.real
            (((openRepresentative E) ∆ torusGraphRegion (c i : Cover) (n i) (g i)) ∩
              Metric.ball (quotientMap (c i : Cover)) s) ≤
              (r i)^3*(e i)^2*(D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))))) ∧
        Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) R,
          (graphNormalize (r (ψ i)) (e (ψ i)) (m (ψ i)) (g (ψ i)) y-u y)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ y in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u y-fderiv ℝ u 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨R₀,D,hR₀,hD,happ⟩ := isMinimizerAt_smooth_trapped_approximation hV hE hmin
  obtain ⟨R₁,A,hR₁,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨Q,hQ,hQs⟩ := exists_small_planeSquare
  obtain ⟨R,C,hR,hC,hRQ,hharm⟩ := planeSquare_H1_strong_harmonic hQ
  let M := 16*Q^2*‖planeProductCoordinates.symm.toContinuousLinearMap‖^2*D
  have hMs : 0 ≤ M := by dsimp [M]; positivity
  have hRR : min R (1/8) ≤ 4*R := (min_le_left _ _).trans (by linarith)
  refine ⟨min (min R₀ R₁) (1/4),Q,min R (1/8),D,M,C,by positivity,hQ,by positivity,
    min_le_right _ _,hD,hMs,hC,(Metric.ball_subset_ball hRR).trans hRQ,?_⟩
  intro μ hμ H hH N hN hp hu c n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt
  have hr₀ (i) : r i ≤ R₀ := (hrr i).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ (i) : r i ≤ R₁ := (hrr i).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrs (i) : r i < 3/8 := lt_of_le_of_lt ((hrr i).trans (min_le_right _ _)) (by norm_num)
  have ha (i) := harea μ hμ (quotientMap (c i : Cover)) (r i) (hr i) (hr₁ i)
  have hgraphs (i) := happ μ hμ N hN hp hu (c i) (n i) (hn i) (r i) (α i) (e i)
    (hr i) (hr₀ i) (hα0 i) (hα i) (he i) (hes i) (htrap i) (htilt i)
  choose g hg hL hh henergy herror using hgraphs
  have hmeans (i) := smooth_graph_normalized_H1 (hg i) (hL i) (hr i) (he i) hQ hQs (hh i)
    (by simpa only [mul_one_div] using henergy i)
  choose m hm hgrad hval using hmeans
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  let L (i : ℕ) : ℝ≥0 := ⟨(e i)⁻¹,inv_nonneg.mpr (he i).le⟩*1
  have hfL (i) : LipschitzWith (L i) (f i) := graphNormalize_lipschitz (hL i) (hr i) (he i) (m i)
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hHU (w : WallVariation) : normalFirstVariation μ w = H*directionalFlux (openRepresentative E) w.coordinate w.function := by
    rw [directionalFlux_congr_ae hUE]
    exact hH w
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using (hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))
  have hcol (i) : (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight (openRepresentative E) (quotientMap (c i : Cover)) (n i) (r i) y|) ≤
      B i*(r i)^3*(e i)^2 := by
    exact (herror i).1.trans_eq (by dsimp [B]; ring)
  have hw := weakCMC_normalized_sequence_harmonic (isOpen_openRepresentative E) hμU hHU hN hp hu
    c n r α e m B g A hn hr hrs hα he htrap htilt ha (fun i ↦ (hg i).continuous)
    hcol helim hBlim hrel
  obtain ⟨ψ,u,hψ,huS,hconv,huE⟩ := hharm f L hfL M D hD hval hgrad
    (fun φ hφ hc hs ↦ hw φ hφ hc (hs.trans (hRQ.trans (hQs.trans (Metric.ball_subset_ball (by norm_num))))))
  refine ⟨m,g,ψ,u,hψ,huS,?_,?_,huE⟩
  · intro i
    exact ⟨hg i,hL i,hh i,hm i,hgrad i,hval i,(herror i).2⟩
  · exact strongL2_restrict_ball (fun i ↦ (graphNormalize_contDiff (hg (ψ i)) _ _ _).continuous)
      huS.continuous (min_le_left _ _) hconv

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVMovingTrappedDecay
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapped_sequential_decay_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,Q,R,D,M,C,hr₀,hQ,hR,hRs,hD,hM,hC,hRQ,hg⟩ :=
    isMinimizerAt_trapped_harmonic_graphs hV hE hmin
  refine ⟨min r₀ (1/4),R,32*C*M,by positivity,hR,hRs,by positivity,?_⟩
  intro μ hμ H hH N hN hp hu c n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt θ ε hθ hθR hε
  obtain ⟨m,g,ψ,u,hψ,huS,hdata,hconv,huE⟩ :=
    hg μ hμ H hH N hN hp hu c n r α e hn hr (fun i ↦ (hrr i).trans (min_le_left _ _)) hα0 hα he hes hαlim helim hrel htrap htilt
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  have hf (i) : ContDiff ℝ (⊤ : ℕ∞) (f i) := graphNormalize_contDiff (hdata i).1 _ _ _
  let p := fderiv ℝ u 0
  let A := 2*D+2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 (2*θ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henergy (i) : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A :=
    graph_relative_energy_bound (hf i) ((Metric.ball_subset_ball hθR).trans hRQ) (hdata i).2.2.2.2.1 p
  have hmlim : Tendsto m atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hαlim
    exact Eventually.of_forall fun i ↦ (hdata i).2.2.2.1
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hh := hrel.mul (helim.pow 2)
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 (he _).ne'), zero_pow (by norm_num : 2 ≠ 0),mul_zero] using hh
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))+e i
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      ((hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))).add helim
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hminU := (isMinimizerAt_congr_ae hUE).mpr hmin
  have hmismatch (i) : sublevelVolume
      ((openRepresentative E) ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
      (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i := by
    rw [show graphRescale (r i) (e i) (m i) (f i) = g i from graphRescale_normalize (hr i).ne' (he i).ne' _ _]
    have hsmall : r i*(2*θ) ≤ 1/4 := by
      have hri := (hrr i).trans (min_le_right _ _)
      nlinarith [mul_le_mul_of_nonneg_left (hθR.trans hRs) (hr i).le]
    unfold sublevelVolume
    rw [sublevelRegion_radialSquared (mul_nonneg (hr i).le (by positivity)) hsmall,cubeBall_eq_metricBall (by linarith : r i*(2*θ) ≤ 3/8)]
    apply ((hdata i).2.2.2.2.2.2 _ ?_).trans_lt
    · dsimp [B]
      nlinarith [mul_pos (pow_pos (hr i) 3) (pow_pos (he i) 3)]
    · calc
        _ ≤ r i*(1/4) := mul_le_mul_of_nonneg_left ((hθR.trans hRs).trans (by norm_num)) (hr i).le
        _ = _ := by ring
  have hconv' := strongL2_restrict_ball (fun i ↦ (hf (ψ i)).continuous) huS.continuous hθR hconv
  obtain ⟨χ,hχ,hdec⟩ := isMinimizerAt_sequential_oriented_decay hV
    (isOpen_openRepresentative E).measurableSet hminU hμU
    (c ∘ ψ) (r ∘ ψ) (e ∘ ψ) (m ∘ ψ) (α ∘ ψ) (B ∘ ψ) (n ∘ ψ) (f ∘ ψ)
    (fun i ↦ hr (ψ i)) (fun i ↦ he (ψ i)) (fun i ↦ hn (ψ i)) (fun i ↦ hf (ψ i))
    (hrlim.comp hψ.tendsto_atTop) (helim.comp hψ.tendsto_atTop)
    (hmlim.comp hψ.tendsto_atTop) (hαlim.comp hψ.tendsto_atTop) (hBlim.comp hψ.tendsto_atTop)
    (hrel.comp hψ.tendsto_atTop) hθ huS p hA (fun i ↦ henergy (ψ i)) (huE (2*θ) (by positivity)) hconv'
    (fun i y _ ↦ graphNormalize_height (hr (ψ i)) (he (ψ i)).ne' _ ((hdata (ψ i)).2.2.1) y)
    (fun i ↦ hmismatch (ψ i)) hε
  refine ⟨ψ ∘ χ,p,hψ.comp hχ,?_⟩
  have heq : 2*(C*M*(2*θ)^4)+ε = 32*C*M*θ^4+ε := by ring
  simpa only [Function.comp_def,heq] using hdec

end CubicTorus.MovingCenter

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay_oai := @OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay_oai
