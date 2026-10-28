-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:51:26.618989+00:00
-- url     : https://prove2.me/submissions/57466567-5957-4053-80bf-278fd5284fa4

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_axialSurface_density_eq_flux
import Theorems.Thm_OAI_CubicTorus_axial_integrated_flux_actual
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_slice_absolutelyContinuous

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

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
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVLipschitzGraph
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

namespace CubicTorus

lemma ediam_metricBall_le (a : Torus) {r : ℝ} (_hr : 0 ≤ r) :
    ediam (Metric.ball a r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hh := dist_triangle_right x y a
  exact hh.trans (by linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy])

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma hausdorff_two_le_open_of_lower_density (σ : FiniteMeasure Torus) (S U : Set Torus)
    (hU : IsOpen U) (hSU : S ⊆ U) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
  classical
  let r : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrR (n) : r n ≤ R := by
    dsimp [r]
    exact div_le_self hR.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have heps : ∀ a ∈ S, ∃ e : ℝ, 0 < e ∧ Metric.ball a e ⊆ U := by
    intro a ha
    exact Metric.isOpen_iff.mp hU a (hSU ha)
  choose e he heU using heps
  let rad (n : ℕ) (a : Torus) : ℝ := if ha : a ∈ S then min (r n) (e a ha) else r n
  have hrad (n : ℕ) (a : Torus) (ha : a ∈ S) : 0 < rad n a := by
    simp only [rad, dite_eq_left ha]
    exact lt_min (hr n) (he a ha)
  have hradle (n : ℕ) (a : Torus) : rad n a ≤ r n := by
    by_cases ha : a ∈ S
    · simp only [rad, dite_eq_left ha]; exact min_le_left _ _
    · simp only [rad, dite_eq_right ha]; exact le_rfl
  have hradU (n : ℕ) (a : Torus) (ha : a ∈ S) : Metric.ball a (rad n a) ⊆ U := by
    apply (Metric.ball_subset_ball ?_).trans (heU a ha)
    simp only [rad, dite_eq_left ha]
    exact min_le_right _ _
  have hex (n : ℕ) := Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id
    (rad n) (r n) (fun a _ ↦ hradle n a) 4 (by norm_num)
  choose u hu hdis hcov using hex
  have hcount (n) : (u n).Countable :=
    (hdis n).countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
      (fun a ha ↦ ⟨a, Metric.mem_ball_self (hrad n a (hu n ha))⟩)
  let : ∀ n, Countable (u n) := fun n ↦ (hcount n).to_subtype
  let t (n : ℕ) (a : u n) : Set Torus := Metric.ball (a : Torus) (4 * rad n a)
  have hdiam' (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * rad n a) := by
    simpa only [t, show (2 : ℝ) * (4 * rad n a) = 8 * rad n a by ring] using
      ediam_metricBall_le (a : Torus) (show 0 ≤ 4 * rad n a from by
        have hh := hrad n a (hu n a.property); positivity)
  have hdiam (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * r n) :=
    (hdiam' n a).trans (ENNReal.ofReal_le_ofReal (by nlinarith [hradle n a]))
  have hcover (n) : S ⊆ ⋃ a : u n, t n a := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov n a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_ball_self (hrad n a ha))⟩
  have hstep (n : ℕ) (a : u n) : ediam (t n a) ^ (2 : ℝ) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := by
    have hrpos := hrad n a (hu n a.property)
    have hlow := hl a (hu n a.property) (rad n a) hrpos ((hradle n a).trans (hrR n))
    have hb : ENNReal.ofReal (c * rad n a ^ 2) ≤
        (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
    calc
      _ = ediam (t n a) ^ (2 : ℕ) := ENNReal.rpow_two _
      _ ≤ (ENNReal.ofReal (8 * rad n a)) ^ (2 : ℕ) := pow_le_pow_left' (hdiam' n a) _
      _ = ENNReal.ofReal (64 / c) * ENNReal.ofReal (c * rad n a ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right hb _
  have hsum (n : ℕ) : (∑' a : u n, ediam (t n a) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
    calc
      _ ≤ ∑' a : u n, ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := ENNReal.tsum_le_tsum (hstep n)
      _ = ENNReal.ofReal (64 / c) *
          (∑' a : u n, (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (⋃ a ∈ u n, Metric.ball a (rad n a)) := by
        congr 1
        exact (measure_biUnion (hcount n) (hdis n)
          (fun _ _ ↦ Metric.isOpen_ball.measurableSet)).symm
      _ ≤ _ := mul_le_mul_right (measure_mono (by
        intro x hx
        obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
        exact hradU n a (hu n ha) hx)) _
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (8 * r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr0.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 S
    (fun n ↦ ENNReal.ofReal (8 * r n)) hlim t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

lemma hausdorff_two_le_measure_of_lower_density (σ : FiniteMeasure Torus) (S : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) S := by
  have h0 : ENNReal.ofReal (64 / c) ≠ 0 := by positivity
  rw [S.measure_eq_iInf_isOpen (σ : Measure Torus),
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro U
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hSU
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf fun hU ↦ hausdorff_two_le_open_of_lower_density σ S U hU hSU hR hc hl

lemma hausdorff_two_null_of_lower_density (σ : FiniteMeasure Torus) (B : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {S : Set Torus} (hSB : S ⊆ B) (hS : (σ : Measure Torus) S = 0) :
    Measure.hausdorffMeasure 2 S = 0 := by
  have hh := hausdorff_two_le_measure_of_lower_density σ S hR hc
    (fun a ha ↦ hl a (hSB ha))
  rw [hS, mul_zero] at hh
  exact le_zero_iff.mp hh

theorem isMinimizerAt_boundary_area_absolutelyContinuous {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (Measure.hausdorffMeasure 2).restrict (frontier (openRepresentative E)) ≪
      (spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  intro S hS
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet]
  apply hausdorff_two_null_of_lower_density (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) hR hc (hl μ hμ)
  · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact inter_subset_right
  · exact measure_mono_null inter_subset_left hS

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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus

lemma directionalFlux_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (i : Fin 3) (g : Cover → ℝ) : directionalFlux E i g = directionalFlux F i g := by
  exact setIntegral_congr_set (liftSet_congr_ae h)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AxisCircleLebesgue
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

lemma axisCircleLebesgue_eq_volume : (axisCircleLebesgue : Measure AxisCircle)=volume := by
  change Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))=volume
  exact (show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle))
    (volume.restrict (Ioc 0 1)) volume from by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_axisCircle_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_singleton_null (x : AxisCircle) : volume ({x} : Set AxisCircle)=0 := by
  let : Fact (0<(1 : ℝ)) := ⟨by norm_num⟩
  have hh := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (ε := (0 : ℝ))
  simpa using hh

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaMarginal
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

lemma torusAxialSplit_symm_apply (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    (torusAxialSplit i).symm (t,y)=WithLp.toLp 2 (i.insertNth t y) := rfl

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialPlanePoint_dist (i : Fin 3) (t : ℝ) (x y : Plane) :
    dist (axialPlanePoint i t x) (axialPlanePoint i t y)=dist x y := by
  simp only [dist_eq_norm]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖^2=‖x-y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succAbove _ i]
    simp [axialPlanePoint,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  nlinarith [norm_nonneg (axialPlanePoint i t x-axialPlanePoint i t y),norm_nonneg (x-y)]

lemma axialPlane_local_antilipschitz (i : Fin 3) (t : ℝ) (a : Plane) :
    AntilipschitzWith 1 (fun y : ball a (1/8 : ℝ) ↦ quotientMap (axialPlanePoint i t y)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one,one_mul,Subtype.dist_eq]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖<1/2 := by
    rw [←dist_eq_norm,axialPlanePoint_dist]
    exact (dist_triangle (x : Plane) a (y : Plane)).trans_lt (by have hy := y.property; rw [mem_ball,dist_comm] at hy; linarith [show dist (x : Plane) a<1/8 from x.property])
  have he : dist (quotientMap (axialPlanePoint i t x)) (quotientMap (axialPlanePoint i t y))=
      dist (axialPlanePoint i t x) (axialPlanePoint i t y) := by
    rw [dist_eq_norm,←quotientMap_sub,←norm_shortestLift,shortestLift_quotientMap hs,dist_eq_norm]
  rw [he,axialPlanePoint_dist]

lemma axialPlane_preimage_hausdorff_null (i : Fin 3) (t : ℝ) {S : Set Torus}
    (hS : Measure.hausdorffMeasure 2 S=0) :
    (volume : Measure Plane) ((fun y ↦ quotientMap (axialPlanePoint i t y)) ⁻¹' S)=0 := by
  let f : Plane → Torus := fun y ↦ quotientMap (axialPlanePoint i t y)
  have hl (a : Plane) : volume (f ⁻¹' S∩ball a (1/8 : ℝ))=0 := by
    have hh := (axialPlane_local_antilipschitz i t a).hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) S
    have hz : Measure.hausdorffMeasure 2 ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=0 := by
      apply le_zero_iff.mp
      simpa [hS] using hh
    have he := (isometry_subtype_coe : Isometry (Subtype.val : ball a (1/8 : ℝ) → Plane)).hausdorffMeasure_image
      (Or.inl (by norm_num : (0 : ℝ)≤2)) ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)
    have ht : Subtype.val '' ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=f ⁻¹' S∩ball a (1/8 : ℝ) := by
      ext y; simp only [mem_image,mem_preimage,mem_inter_iff]; constructor
      · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
      · rintro ⟨hy,hb⟩; exact ⟨⟨y,hb⟩,hy,rfl⟩
    rw [ht,hz] at he
    exact Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Plane) (Measure.hausdorffMeasure 2) he
  obtain ⟨D,hD,hDD⟩ := TopologicalSpace.exists_countable_dense Plane
  have hc : ⋃ a∈D,ball a (1/8 : ℝ)=univ := (dense_iff_iUnion_ball D).mp hDD _ (by norm_num)
  have he : f ⁻¹' S=⋃ a∈D,f ⁻¹' S∩ball a (1/8 : ℝ) := by
    rw [←inter_iUnion₂,hc,inter_univ]
  rw [he]
  exact measure_biUnion_null_iff hD |>.mpr (fun a _ ↦ hl a)

lemma transverse_quotient_measurePreserving :
    MeasurePreserving (fun y : Fin 2 → ℝ ↦ fun j ↦ (y j : AxisCircle))
      ((volume : Measure (Fin 2 → ℝ)).restrict (univ.pi (fun _ ↦ Ico (0 : ℝ) 1))) volume := by
  have hh := measurePreserving_pi (fun _ : Fin 2 ↦ volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 2 ↦ (volume : Measure AxisCircle)) (fun _ ↦ circle_measurePreserving_mk_Ico)
  simpa only [volume_pi,Measure.restrict_pi_pi] using hh

lemma axialSlice_hausdorff_null (i : Fin 3) (t : AxisCircle) {S : Set Torus}
    (hSm : MeasurableSet S) (hS : Measure.hausdorffMeasure 2 S=0) : volume (axialSlice S i t)=0 := by
  induction t using Quotient.inductionOn with | h t =>
    have hp := axialPlane_preimage_hausdorff_null i t hS
    have he : (fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle)))=
        (fun y : Plane ↦ quotientMap (axialPlanePoint i t y)) ∘ (WithLp.toLp 2) := by
      funext y
      apply PiLp.ext
      refine (Fin.forall_iff_succAbove i).mpr ⟨?_,?_⟩
      · simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
      · intro j; simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
    have hnull : volume ((fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle))) ⁻¹' S)=0 := by
      rw [he,preimage_comp]
      exact (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.preimage_null hp
    rw [←transverse_quotient_measurePreserving.map_eq,
      Measure.map_apply transverse_quotient_measurePreserving.measurable (axialSlice_measurable hSm i (t : AxisCircle))]
    exact le_zero_iff.mp ((Measure.restrict_le_self _) |>.trans_eq hnull)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialNormalDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalDensity μ i) :=
  Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

lemma axialNormalDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialNormalDensity μ i) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub (Measure.measurable_rnDeriv _ _).ennreal_toReal

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_integral_eq_interval {f : AxisCircle → ℝ} (hf : AEStronglyMeasurable f volume) :
    (∫ t,f t)=∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  have hm : Measurable (fun t : ℝ ↦ (t : AxisCircle)) := (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := congrArg (fun η : Measure AxisCircle ↦ ∫ t,f t ∂η) axisCircleLebesgue_eq_volume
  change (∫ t,f t ∂Measure.map _ _)=_ at hh
  have hf' : AEStronglyMeasurable f (Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))) := by
    change AEStronglyMeasurable f (axisCircleLebesgue : Measure AxisCircle)
    rwa [axisCircleLebesgue_eq_volume]
  rw [integral_map hm.aemeasurable hf'] at hh
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  exact hh.symm

lemma circle_intervalIntegrable {f : AxisCircle → ℝ} (hf : Integrable f volume) :
    IntervalIntegrable (fun t : ℝ ↦ f (t : AxisCircle)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
  exact ((show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume from
    by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).integrable_comp hf.aestronglyMeasurable).mpr hf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSlice_point_continuous (i : Fin 3) (y : TransverseProduct) :
    Continuous (fun t : AxisCircle ↦ (torusAxialSplit i).symm (t,y)) := by
  change Continuous (fun t : AxisCircle ↦ WithLp.toLp 2 (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (Fin.forall_iff_succAbove (P := fun j : Fin 3 ↦ Continuous (fun t : AxisCircle ↦ (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y) j)) i).mpr ⟨by simp only [Fin.insertNth_apply_same]; exact continuous_id,fun k ↦ by simp only [Fin.insertNth_apply_succAbove]; exact continuous_const⟩ j

lemma isMinimizerAt_boundary_slice_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) (t : AxisCircle) :
    volume (axialSlice (frontier (openRepresentative E)) i t)=0 := by
  let T : Set Torus := {z | z i=t}
  have hT : MeasurableSet T := measurableSet_eq_fun (torus_axis_measurePreserving i).measurable measurable_const
  have ht : (spatialNormalMeasure μ : Measure Torus) T=0 := by
    have hh := ha (axisCircle_singleton_null t)
    change Measure.map _ _ {t}=0 at hh
    rw [Measure.map_apply (normal_axisCircle_continuous i).measurable (measurableSet_singleton t)] at hh
    change Measure.map normalProjection _ T=0
    rw [Measure.map_apply normalProjection_continuous.measurable hT]
    exact hh
  have hh := isMinimizerAt_boundary_area_absolutelyContinuous hV hE hmin hμ ht
  rw [Measure.restrict_apply hT] at hh
  have hs := axialSlice_hausdorff_null i t (hT.inter isClosed_frontier.measurableSet) hh
  have he : axialSlice (T∩frontier (openRepresentative E)) i t=axialSlice (frontier (openRepresentative E)) i t := by
    ext y
    simp [axialSlice,T]
  rwa [he] at hs

lemma axialSliceVolume_continuous_of_boundary_null {U : Set Torus} (hU : MeasurableSet U)
    (i : Fin 3) (hn : ∀ t : AxisCircle,volume (axialSlice (frontier U) i t)=0) :
    Continuous (fun t ↦ (axialSliceVolume U i t).toReal) := by
  let F : AxisCircle → TransverseProduct → ℝ := fun t y ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (t,y))
  have he (t : AxisCircle) : (∫ y,F t y)=(axialSliceVolume U i t).toReal := by
    have hf : F t=(axialSlice U i t).indicator 1 := by
      funext y
      by_cases hy : (torusAxialSplit i).symm (t,y)∈U <;> simp [F,axialSlice,hy]
    rw [hf,integral_indicator_one (axialSlice_measurable hU i t)]
    rfl
  rw [show (fun t ↦ (axialSliceVolume U i t).toReal)=(fun t ↦ ∫ y,F t y) from funext (fun t ↦ (he t).symm)]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun _ ↦ (1 : ℝ))
  · apply Eventually.of_forall
    intro s
    exact (measurable_const.indicator hU |>.comp ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    exact (norm_indicator_le_norm_self (s := U) (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))).trans (by norm_num)
  · exact integrable_const 1
  · have hnb : ∀ᵐ y : TransverseProduct,(torusAxialSplit i).symm (t,y)∉frontier U := by
      rw [ae_iff]
      simpa only [not_not,axialSlice] using hn t
    filter_upwards [hnb] with y hy
    change ContinuousAt (fun s ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))) t
    exact ContinuousAt.comp (f := fun s ↦ (torusAxialSplit i).symm (s,y)) (g := U.indicator (fun _ ↦ (1 : ℝ))) (continuous_const.continuousOn.continuousAt_indicator hy) (axialSlice_point_continuous i y).continuousAt

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ActualAxialFlux
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

lemma circle_ac_oscillation_bound {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b)
    (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|f t-f 0|≤∫ s,|g s| := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume 0 1 := circle_intervalIntegrable hgi
  have hi0 : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume 0 t := hi.mono (by
    rw [uIcc_of_le ht.1,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact fun s hs ↦ ⟨hs.1,hs.2.trans ht.2⟩) le_rfl
  have hi1 : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume t 1 := hi.mono (by
    rw [uIcc_of_le ht.2,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact fun s hs ↦ ⟨ht.1.trans hs.1,hs.2⟩) le_rfl
  have h0 : (∫ s in (0 : ℝ)..t,g (s : AxisCircle))=f t-f 0 := by
    rw [←(hf 0 t).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs hst
    exact (hs (by have hh := uIoc_subset_uIcc hst; rw [uIcc_of_le ht.1] at hh; exact ⟨hh.1,hh.2.trans ht.2⟩)).deriv.symm
  have h1 : (∫ s in t..1,g (s : AxisCircle))=f 1-f t := by
    rw [←(hf t 1).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs hst
    exact (hs (by have hh := uIoc_subset_uIcc hst; rw [uIcc_of_le ht.2] at hh; exact ⟨ht.1.trans hh.1,hh.2⟩)).deriv.symm
  have hb0 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s : ℝ ↦ g (s : AxisCircle)) ht.1
  have hb1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s : ℝ ↦ g (s : AxisCircle)) ht.2
  rw [h0,Real.norm_eq_abs] at hb0
  rw [h1,Real.norm_eq_abs,show f 1=f 0 from by simpa using hp 0,abs_sub_comm] at hb1
  have hh := add_le_add hb0 hb1
  rw [intervalIntegral.integral_add_adjacent_intervals hi0.norm hi1.norm] at hh
  rw [circle_integral_eq_interval hgi.abs.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs,two_mul] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalTransverseLength
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

lemma axialPerimeterDensity_nonneg (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) :
    0≤axialPerimeterDensity μ i t := ENNReal.toReal_nonneg

lemma axialPerimeterDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialPerimeterDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
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

lemma axialSecondDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialSecondDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

lemma sqrt_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma sqrt_square_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
    (ne_of_gt hp) using 1
  · rfl
  · dsimp
    ring

lemma cutoff_pos : 0 < cutoff := by
  unfold cutoff
  positivity

lemma cutoff_sq : cutoff ^ 2 = 48 / 49 := by
  norm_num [cutoff, div_pow]

lemma cutoff_lt_one : cutoff < 1 := by
  nlinarith [cutoff_sq, cutoff_pos]

lemma rawWeight_lower {x : ℝ} (hx : x ∈ Ico 0 1) : ell ≤ rawWeight x := by
  have hrad : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hs2 := Real.sq_sqrt (le_of_lt hrad)
  unfold rawWeight ell lambda
  apply (le_div_iff₀ hs).2
  nlinarith [sq_nonneg (7 * Real.sqrt (1 - x ^ 2) - 1)]

lemma hasDerivAt_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt rawWeight
      (x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3)) x := by
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hs0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hh := ((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 98 * x * hs2

lemma continuousOn_rawWeight : ContinuousOn rawWeight (Icc 0 cutoff) := by
  have hs : ∀ x ∈ Icc 0 cutoff, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    apply ne_of_gt (Real.sqrt_pos.2 _)
    have hxl : x < 1 := lt_of_le_of_lt hx.2 cutoff_lt_one
    nlinarith [hx.1, sq_nonneg x]
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn) hs

lemma antitoneOn_rawWeight : AntitoneOn rawWeight (Icc 0 cutoff) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x =>
    x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3))
    (convex_Icc 0 cutoff) continuousOn_rawWeight ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_rawWeight ⟨hx.1, lt_trans hx.2 cutoff_lt_one⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx.1)
    have hsq : x ^ 2 ≤ cutoff ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hx.1) (le_of_lt hx.2) 2
    nlinarith [cutoff_sq]

lemma weight_mem {x : ℝ} (hx : 0 ≤ x) : weight x ∈ Icc ell 1 := by
  have hm : min x cutoff ∈ Icc 0 cutoff :=
    ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩
  constructor
  · exact rawWeight_lower ⟨hm.1, lt_of_le_of_lt hm.2 cutoff_lt_one⟩
  · have hh := antitoneOn_rawWeight ⟨le_rfl, le_of_lt cutoff_pos⟩ hm hm.1
    simpa [weight, rawWeight] using hh

end CubicTorus.Nesting

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SharpSectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set
namespace CubicTorus.Nesting

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  apply continuousOn_rawWeight.comp (continuous_id.min continuous_const).continuousOn
  intro x hx
  exact ⟨le_min hx cutoff_pos.le,min_le_right _ _⟩

end CubicTorus.Nesting

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_mul_unit {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → ℝ} (hf : Integrable f ν) (hg : Measurable g) (hb : ∀ x,|g x|≤1) :
    Integrable (fun x ↦ f x*g x) ν := by
  apply Integrable.mono' hf.abs (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_nesting_weight_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (hn : ∀ x,0≤f x) : Measurable (fun x ↦ Nesting.weight (f x)) := by
  have hc : Continuous (fun t : ℝ ↦ Nesting.weight (max t 0)) :=
    Nesting.continuousOn_weight.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have hh := hc.measurable.comp hf
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact congrArg Nesting.weight (max_eq_left (hn x)).symm

lemma axial_weighted_normal_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (fun t ↦ Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|) := by
  have hf := measurable_nesting_weight_comp
    ((axialSecondDensity_measurable μ i).div (axialPerimeterDensity_measurable μ i))
    (fun t ↦ div_nonneg ENNReal.toReal_nonneg (axialPerimeterDensity_nonneg μ i t))
  apply Integrable.mono' (axialNormalDensity_integrable μ i).abs
    (hf.mul (axialNormalDensity_measurable μ i).abs).aestronglyMeasurable
  filter_upwards [] with t
  have hm := Nesting.weight_mem (div_nonneg (show 0≤axialSecondDensity μ i t from ENNReal.toReal_nonneg)
    (axialPerimeterDensity_nonneg μ i t))
  have hn : 0≤Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t) :=
    (by norm_num [Nesting.ell] : (0 : ℝ)≤Nesting.ell).trans hm.1
  change ‖Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
    |axialNormalDensity μ i t|‖≤|axialNormalDensity μ i t|
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hn,abs_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) hm.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma one_lipschitz_comp_ac {P f : ℝ → ℝ} (hP : LipschitzWith 1 P)
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ P (f t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := hf ε hε
  refine ⟨δ,hδ,fun E hE hsum ↦ lt_of_le_of_lt ?_ (hh E hE hsum)⟩
  apply Finset.sum_le_sum
  intro i hi
  simpa using hP.dist_le_mul (f (E.2 i).1) (f (E.2 i).2)

lemma bounded_primitive_lipschitz {γ : ℝ → ℝ} (hc : Continuous γ)
    (hb : ∀ x,|γ x|≤1) : LipschitzWith 1 (fun r ↦ ∫ s in (0 : ℝ)..r,γ s) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := y)) (hc.intervalIntegrable (μ := volume) (a := y) (b := x))
  have hbb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (f := γ) (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hb z)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,Real.norm_eq_abs] at hbb ⊢
  rw [show (∫ s in (0 : ℝ)..x,γ s)-(∫ s in (0 : ℝ)..y,γ s)=∫ s in y..x,γ s by linarith only [hh] ]
  exact hbb

theorem circle_ac_weighted_oscillation {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hc : Continuous f)
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {γ : ℝ → ℝ} (hγ : Continuous γ) (hγb : ∀ x,γ x∈Icc 0 1)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|∫ y in f 0..f t,γ y|≤∫ s,γ (hp.lift s)*|g s| := by
  let P : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..r,γ s
  have hPb (x : ℝ) : |γ x|≤1 := by rw [abs_of_nonneg (hγb x).1]; exact (hγb x).2
  have hP : LipschitzWith 1 P := bounded_primitive_lipschitz hγ hPb
  have hPd (x : ℝ) : HasDerivAt P (γ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hγ.intervalIntegrable (μ := volume) 0 x)
      hγ.stronglyMeasurable.stronglyMeasurableAtFilter hγ.continuousAt
  have hFp : Function.Periodic (fun t ↦ P (f t)) 1 := fun t ↦ congrArg P (hp t)
  have hFi (a b : ℝ) := one_lipschitz_comp_ac hP (hf a b)
  have hgm : Measurable (fun s : AxisCircle ↦ γ (hp.lift s)) :=
    hγ.measurable.comp (continuous_periodic_lift hp hc).measurable
  have hwi : Integrable (fun s : AxisCircle ↦ γ (hp.lift s)*g s) := by
    simpa only [mul_comm] using integrable_mul_unit hgi hgm (fun s ↦ hPb _)
  have hwd : ∀ᵐ r : ℝ,r∈Icc (0 : ℝ) 1 → HasDerivAt (fun t ↦ P (f t))
      (γ (hp.lift (r : AxisCircle))*g (r : AxisCircle)) r := by
    filter_upwards [hd] with r hr hri
    exact (hPd (f r)).comp r (hr hri)
  have hh := circle_ac_oscillation_bound hFp hFi hwi hwd ht
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hγ.intervalIntegrable (μ := volume) (a := 0) (b := f 0)) (hγ.intervalIntegrable (μ := volume) (a := f 0) (b := f t))
  have hPe : P (f t)-P (f 0)=∫ y in f 0..f t,γ y := by
    dsimp only [P]
    linarith only [he]
  rw [hPe] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with s
  rw [abs_mul,abs_of_nonneg (hγb _).1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma real_measure_le_of_unit_continuous {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hh : ∀ f : ℝ → ℝ,Continuous f → (∀ x,f x∈Icc 0 1) →
      (∫ x,f x ∂μ)≤∫ x,f x ∂ν) : μ≤ν := by
  have hcompact ⦃K : Set ℝ⦄ (hK : IsCompact K) : μ K≤ν K := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
    have hνK : ν K≠⊤ := hν.ne
    have hμK : μ K≠⊤ := hK.measure_lt_top.ne
    obtain ⟨V,pV1,pV2,pV3⟩ : ∃ V⊇K,IsOpen V ∧ ν V≤ν K+ε :=
      exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    suffices μ.real K≤ν.real K+ε by
      rwa [←ENNReal.toReal_le_toReal,ENNReal.toReal_add,ENNReal.coe_toReal]
      all_goals finiteness
    obtain ⟨f,hf1,hf2,hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    have hfiμ : Integrable f μ := (f.continuous.integrable_of_hasCompactSupport (hasCompactSupport_def.mpr hf2))
    have hfiν : Integrable f ν := (f.continuous.integrable_of_hasCompactSupport (hasCompactSupport_def.mpr hf2))
    have hfV (x : ℝ) : f x≤V.indicator 1 x := by
      by_cases hx : x∈tsupport f
      · simp [(hf3.1 hx),(hf3.2 x).2]
      · simp [image_eq_zero_of_notMem_tsupport hx,Set.indicator_nonneg]
    have hfK (x : ℝ) : K.indicator 1 x≤f x := by
      by_cases hx : x∈K
      · simp [hx,hf1 hx]
      · simp [hx,(hf3.2 x).1]
    calc
      μ.real K=(∫ x,K.indicator 1 x ∂μ) := (integral_indicator_one hK.measurableSet).symm
      _≤∫ x,f x ∂μ := integral_mono
        ((integrable_const (1 : ℝ)).indicator hK.measurableSet) hfiμ hfK
      _≤∫ x,f x ∂ν := hh f f.continuous hf3.2
      _≤∫ x,V.indicator 1 x ∂ν := integral_mono hfiν
        ((integrable_const (1 : ℝ)).indicator pV2.measurableSet) hfV
      _≤(ν K).toReal+↑ε := by
        rwa [integral_indicator_one pV2.measurableSet,measureReal_def,
          ←ENNReal.coe_toReal,←ENNReal.toReal_add,ENNReal.toReal_le_toReal]
        all_goals finiteness
  intro s
  apply (measure_mono (subset_toMeasurable ν s)).trans
  have hsm := measurableSet_toMeasurable ν s
  rw [hsm.measure_eq_iSup_isCompact μ]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKs
  apply iSup_le
  intro hK
  exact (hcompact hK).trans (by simpa only [measure_toMeasurable] using measure_mono (μ := ν) hKs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem circle_ac_measurable_weight_integrable {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hc : Continuous f)
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγgi : Integrable (fun s ↦ γ (hp.lift s)*|g s|))
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|∫ y in f 0..f t,γ y|≤∫ s,γ (hp.lift s)*|g s| := by
  let ρ : Measure AxisCircle := volume.withDensity (fun s ↦ ENNReal.ofReal |g s|)
  have hfin : (∫⁻ s,ENNReal.ofReal |g s|)≠⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun s ↦ abs_nonneg (g s)))).mp hgi.abs.2).ne
  let : IsFiniteMeasure ρ := isFiniteMeasure_withDensity hfin
  let ν : Measure ℝ := Measure.map hp.lift ρ
  let μ : Measure ℝ := (2 : ℝ≥0∞) • volume.restrict (uIoc (f 0) (f t))
  have : IsFiniteMeasure (volume.restrict (uIoc (f 0) (f t))) := by
    unfold uIoc
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsFiniteMeasure μ := by
    exact Measure.smul_finite _ (by norm_num)
  have hpc : Continuous hp.lift := continuous_periodic_lift hp hc
  have hpair (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
      (∫ y,ψ y ∂ν)=∫ s,ψ (hp.lift s)*|g s| := by
    rw [show ν=Measure.map hp.lift ρ from rfl,
      integral_map hpc.measurable.aemeasurable hψ.aestronglyMeasurable]
    rw [show ρ=volume.withDensity (fun s ↦ ENNReal.ofReal |g s|) from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hgi.aemeasurable.abs.ennreal_ofReal
        (Eventually.of_forall (fun s ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,mul_comm]
  have hleft (ψ : ℝ → ℝ) (hn : ∀ x,0≤ψ x) :
      (∫ y,ψ y ∂μ)=2*|∫ y in f 0..f t,ψ y| := by
    rw [show μ=(2 : ℝ≥0∞) • volume.restrict (uIoc (f 0) (f t)) from rfl,
      integral_smul_measure,intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      abs_of_nonneg (integral_nonneg hn)]
    norm_num
  have horder : μ≤ν := by
    apply real_measure_le_of_unit_continuous
    intro ψ hψ hb
    rw [hpair ψ hψ.measurable,hleft ψ (fun x ↦ (hb x).1)]
    exact circle_ac_weighted_oscillation hp hc hf hgi hd hψ hb ht
  have hγi : Integrable γ ν := by
    apply (integrable_map_measure hγ.aestronglyMeasurable hpc.measurable.aemeasurable).mpr
    apply (integrable_withDensity_iff_integrable_smul₀'
      hgi.aemeasurable.abs.ennreal_ofReal
      (Eventually.of_forall (fun s ↦ ENNReal.ofReal_lt_top))).mpr
    simpa only [Function.comp_apply,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,mul_comm] using hγgi
  have hh := integral_mono_measure horder (Eventually.of_forall hγn) hγi
  rwa [hpair γ hγ,hleft γ hγn] at hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
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

theorem isMinimizerAt_measurable_weighted_area_bound_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t))
    {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) :
    Nesting.lambda*axialTransverseMass μ i+
      2*|∫ y in (axialSliceVolume (openRepresentative E) i 0).toReal..
        (axialSliceVolume (openRepresentative E) i (τ : AxisCircle)).toReal,γ y|≤
      (perimeter E).toReal := by
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hHO (D : Periodic.Variation) : Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by rw [directionalFlux_congr_ae hOE]; exact hH D
  let v : AxisCircle → ℝ := fun t ↦ (axialSliceVolume O i t).toReal
  have hv : Continuous v := axialSliceVolume_continuous_of_boundary_null hO i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  have hp : Function.Periodic (fun t : ℝ ↦ v (t : AxisCircle)) 1 := by
    intro t
    change v (((t+1 : ℝ) : AxisCircle))=v (t : AxisCircle)
    rw [AddCircle.coe_add_period]
  have hc : Continuous (fun t : ℝ ↦ v (t : AxisCircle)) := hv.comp (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨hac,hd⟩ := isMinimizerAt_slice_absolutelyContinuous hV hE hmin hμ i ha
  have hlift (t : AxisCircle) : hp.lift t=v t := by
    induction t using Quotient.inductionOn with | h t => rfl
  have hwEq : (fun t ↦ Nesting.weight (actualAxialFlux O μ H i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|)=ᵐ[volume](fun t ↦ Nesting.weight
        (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|) := by
    filter_upwards [axialSurface_density_eq_flux hO hHO i] with t ht
    rw [←ht]
    rfl
  have hlarge := (axial_weighted_normal_integrable μ i).congr hwEq.symm
  have hsmall : Integrable (fun t ↦ γ (v t)*|axialNormalDensity μ i t|) := by
    apply hlarge.mono' ((hγ.comp hv.measurable).mul (axialNormalDensity_measurable μ i).abs).aestronglyMeasurable
    filter_upwards [hγw] with t ht
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (hγn _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hwint : Integrable (fun t ↦ γ (hp.lift t)*|(-axialNormalDensity μ i) t|) := by
    simpa only [hlift,Pi.neg_apply,abs_neg] using hsmall
  have hb := circle_ac_measurable_weight_integrable hp hc hac (axialNormalDensity_integrable μ i).neg hd hγ hγn hwint hτ
  simp only [hlift,Pi.neg_apply,abs_neg,AddCircle.coe_zero] at hb
  have him := integral_mono_ae hsmall hlarge (by
    filter_upwards [hγw] with t ht
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hflux := axial_integrated_flux_actual hO hμO hHO i ha
  rw [perimeter_congr_ae hOE] at hflux
  change _≤(perimeter E).toReal
  have hh := hb.trans him
  exact (add_le_add le_rfl hh).trans hflux

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound_oai := @OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound_oai
