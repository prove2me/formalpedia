-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:17:36.920235+00:00
-- url     : https://prove2.me/submissions/ac52faff-0d99-41ad-8161-734691aa1a9a

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_lipschitz_approximation_with_cones
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normalGraph_good_energy
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density

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

lemma shortestLift_eq_of_lift {a : Torus} {v : Cover} (hv : quotientMap v = a)
    (hn : ‖v‖ < 1 / 2) : shortestLift a = v := by rw [← hv, shortestLift_quotientMap hn]

lemma shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    shortestLift (x - y) = shortestLift (x - c) - shortestLift (y - c) := by
  apply shortestLift_eq_of_lift
  · simp only [quotientMap_sub, quotientMap_shortestLift]; abel
  · exact (norm_sub_le _ _).trans_lt (by
      simpa only [norm_shortestLift, ← dist_eq_norm] using hxy)

lemma dist_shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    dist (shortestLift (x - c)) (shortestLift (y - c)) = dist x y := by
  rw [dist_eq_norm, ← shortestLift_sub_local hxy, norm_shortestLift, ← dist_eq_norm]

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

lemma normalPlaneProjection_sub (n v w : Cover) :
    normalPlaneProjection n (v - w) = normalPlaneProjection n v - normalPlaneProjection n w := by
  simp only [normalPlaneProjection, inner_sub_right, sub_smul]
  abel

lemma norm_le_two_normalPlaneProjection {n v : Cover} (hn : ‖n‖ = 1)
    {ε : ℝ} (hε : ε ≤ 1 / 2) (hc : |⟪n, v⟫| ≤ ε * ‖v‖) :
    ‖v‖ ≤ 2 * ‖normalPlaneProjection n v‖ := by
  have hh := norm_add_le (normalPlaneProjection n v) (⟪n, v⟫ • n)
  rw [show normalPlaneProjection n v + ⟪n, v⟫ • n = v by simp [normalPlaneProjection],
    norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
  nlinarith [norm_nonneg v]

end CubicTorus

end
end

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_sq_norm_sub_normal {σ : FiniteMeasure Torus} {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) :
    Integrable (fun x ↦ ‖N x - n‖ ^ 2) (σ : Measure Torus) := by
  apply Integrable.of_bound ((hN.sub_const n).norm.pow_const 2).aestronglyMeasurable ((1 + ‖n‖) ^ 2)
  filter_upwards [hn] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [hx] using norm_sub_le (N x) n

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_lipschitz {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) : LipschitzWith (1 + K) (normalGraph n g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : normalGraph n g x - normalGraph n g y =
      normalPlaneEmbedding n (x - y) + (g x - g y) • n := by
    change normalPlaneLinearIsometry n x + g x • n -
      (normalPlaneLinearIsometry n y + g y • n) = _
    rw [show normalPlaneEmbedding n (x - y) =
      normalPlaneLinearIsometry n x - normalPlaneLinearIsometry n y from (normalPlaneLinearIsometry n).map_sub x y, sub_smul]
    abel
  have hh := norm_add_le (normalPlaneEmbedding n (x - y)) ((g x - g y) • n)
  rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one] at hh
  have hb := hg.norm_sub_le x y
  rw [dist_eq_norm, he, dist_eq_norm]
  change ‖normalPlaneEmbedding n (x - y) + (g x - g y) • n‖ ≤ (1 + (K : ℝ)) * ‖x - y‖
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
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

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

lemma normalPlaneCoordinates_torus_lipschitz (n : Cover) (a : Torus) :
    LipschitzOnWith 1 (fun x ↦ normalPlaneCoordinates n (shortestLift (x - a)))
      (Metric.ball a (1 / 4)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul
    (shortestLift (x - a)) (shortestLift (y - a))
  have hxy : dist x a + dist y a < 1 / 2 := by
    change dist x a < 1 / 4 at hx
    change dist y a < 1 / 4 at hy
    linarith
  simpa only [dist_shortestLift_sub_local hxy] using hh

lemma exists_frontier_on_interval {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : ℝ → X} (hf : Continuous f)
    {s t : ℝ} (hst : s ≤ t) (hs : f s ∈ U) (ht : f t ∉ closure U) :
    ∃ u ∈ Icc s t, f u ∈ frontier U := by
  by_contra! hn
  have hsub : f '' Icc s t ⊆ U ∪ (closure U)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases h : f u ∈ closure U
    · left
      have hh := hn u hu
      rw [frontier, hU.interior_eq, Set.mem_sdiff, not_and] at hh
      exact not_not.mp (hh h)
    · exact Or.inr h
  have hd : Disjoint U (closure U)ᶜ := disjoint_compl_right.mono_left subset_closure
  rcases (isPreconnected_Icc.image f hf.continuousOn).subset_or_subset hU
      isClosed_closure.isOpen_compl hd hsub with h | h
  · exact ht (subset_closure (h ⟨t, ⟨hst, le_rfl⟩, rfl⟩))
  · exact h ⟨s, ⟨le_rfl, hst⟩, rfl⟩ (subset_closure hs)

lemma trapped_boundary_projects_disk {U : Set Torus} (hU : IsOpen U)
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U) :
    Metric.ball (0 : Plane) (r / 4) ⊆
      (fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) ''
        (frontier U ∩ Metric.ball a (r / 2)) := by
  intro y hy
  have hyn : ‖y‖ < r / 4 := by simpa using hy
  let f : ℝ → Torus := fun t ↦ quotientMap (normalPlaneEmbedding n y + t • n) + a
  have hf : Continuous f :=
    (continuous_quotientMap.comp (continuous_const.add (continuous_id.smul continuous_const))).add continuous_const
  have hsize (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ‖normalPlaneEmbedding n y + t • n‖ < r / 2 := by
    have hab : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    linarith
  have hl (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      shortestLift (f t - a) = normalPlaneEmbedding n y + t • n := by
    dsimp [f]
    rw [add_sub_cancel_right]
    apply shortestLift_quotientMap
    exact (hsize t ht).trans (by linarith)
  have hd (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) : dist (f t) a < r / 2 := by
    rw [dist_eq_norm, ← norm_shortestLift, hl t ht]
    exact hsize t ht
  have hm : -r / 4 ∈ Icc (-r / 4) (r / 4) := ⟨le_rfl, by linarith⟩
  have hp : r / 4 ∈ Icc (-r / 4) (r / 4) := ⟨by linarith, le_rfl⟩
  have hinner (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ⟪n, shortestLift (f t - a)⟫ = t := by
    rw [hl t ht, inner_add_right, normalPlaneEmbedding_inner hn,
      inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  have hs : f (-r / 4) ∈ U := by
    apply htrap.2
    exact ⟨(hd _ hm).trans (by linarith), by
      rw [inner_neg_left, hinner _ hm]
      nlinarith [mul_lt_mul_of_pos_right hε hr]⟩
  have ht : f (r / 4) ∉ closure U := by
    apply htrap.1
    exact ⟨(hd _ hp).trans (by linarith), by
      rw [hinner _ hp]
      nlinarith [mul_lt_mul_of_pos_right hε hr]⟩
  obtain ⟨t, hti, htb⟩ := exists_frontier_on_interval hU hf (by linarith : -r / 4 ≤ r / 4) hs ht
  refine ⟨f t, ⟨htb, hd t hti⟩, ?_⟩
  simp [hl t hti, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

lemma plane_projection_volume_le_perimeter (σ : FiniteMeasure Torus)
    (B : Set Torus) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    (n : Cover) (a : Torus) (S : Set Torus) (hS : S ⊆ B)
    (hsmall : S ⊆ Metric.ball a (1 / 4)) :
    (volume : Measure Plane)
      ((fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) '' S) ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) * (σ : Measure Torus) S := by
  have hp := ((normalPlaneCoordinates_torus_lipschitz n a).mono hsmall).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 2)
  have hp' : Measure.hausdorffMeasure 2
      ((fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) '' S) ≤
      Measure.hausdorffMeasure 2 S := by simpa using hp
  have hl' := hausdorff_two_le_measure_of_lower_density σ S hR hc (fun x hx ↦ hl x (hS hx))
  rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure Plane) (Measure.hausdorffMeasure 2),
    Measure.smul_apply]
  change (planeAreaFactor : ℝ≥0∞) * _ ≤ _
  calc
    _ ≤ (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 S := mul_le_mul_right hp' _
    _ ≤ (planeAreaFactor : ℝ≥0∞) * (ENNReal.ofReal (64 / c) * (σ : Measure Torus) S) :=
      mul_le_mul_right hl' _
    _ = _ := (mul_assoc _ _ _).symm

lemma trapped_graph_holes_volume_le
    {U : Set Torus} (hU : IsOpen U) (σ : FiniteMeasure Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ frontier U, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫) :
    (volume : Measure Plane) {y ∈ Metric.ball (0 : Plane) (r / 4) |
      a + quotientMap (normalGraph n g y) ∉ frontier U} ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
  let Q : Torus → Plane := fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))
  have hcover : {y ∈ Metric.ball (0 : Plane) (r / 4) |
      a + quotientMap (normalGraph n g y) ∉ frontier U} ⊆
      Q '' ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := trapped_boundary_projects_disk hU a hn hr hrsmall hε htrap hy.1
    have hxS : x ∉ S := by
      intro hm
      have hg : normalGraph n g y = shortestLift (x - a) := by
        rw [← hxy, normalGraph, hS x hm]
        exact normalPlaneCoordinates_reconstruct hn _
      apply hy.2
      rw [hg, quotientMap_shortestLift, add_sub_cancel]
      exact hx.1
    exact ⟨x, ⟨hx, hxS⟩, hxy⟩
  apply (measure_mono hcover).trans
  apply plane_projection_volume_le_perimeter σ (frontier U) hR hc hl n a _
    (fun x hx ↦ hx.1.1)
  intro x hx
  exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ 1 / 4)) hx.1.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normalGraph_full_energy {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
        LipschitzWith K g → K ≤ 1 → ∀ a : Torus, ∀ r ε : ℝ,
        0 < r → r < 1 / 2 → ε < 1 / 4 →
        (normalCap a n r (ε * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (ε * r) ⊆ openRepresentative E) →
        (∀ y ∈ Metric.ball (0 : Plane) (r / 4), |g y| ≤ r / 4) →
      ∀ S : Set Torus,
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) →
      (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
        ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤
        C * ((∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
          (spatialNormalMeasure μ : Measure Torus)
            ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S)) := by
  obtain ⟨C₀, hC₀, hgood⟩ := isMinimizerAt_normalGraph_good_energy hV hE hmin
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C₁ : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)
  let C := C₀ + C₁
  refine ⟨C, by dsimp [C, C₁]; finiteness, ?_⟩
  intro μ hμ N hN hp hn n hnorm g K hg hK a r ε hr hrs hε htrap hheight S hS
  let U := openRepresentative E
  let Ω : Set Plane := Metric.ball 0 (r / 4)
  let F : Plane → Torus := fun y ↦ a + quotientMap (normalGraph n g y)
  let D : Set Plane := {y ∈ Ω | F y ∈ frontier U}
  let H : Set Plane := {y ∈ Ω | F y ∉ frontier U}
  have hF : Continuous F :=
    continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hnorm hg).continuous)
  have hD : MeasurableSet D := measurableSet_ball.inter (isClosed_frontier.measurableSet.preimage hF.measurable)
  have hsize (y : Plane) (hy : y ∈ Ω) : ‖normalGraph n g y‖ < r / 2 := by
    have hyn : ‖y‖ < r / 4 := by simpa [Ω] using hy
    have hh := norm_add_le (normalPlaneEmbedding n y) (g y • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hnorm, mul_one, Real.norm_eq_abs] at hh
    change ‖normalPlaneEmbedding n y + g y • n‖ < r / 2
    linarith [hheight y hy]
  have hsmall (y : Plane) (hy : y ∈ D) : ‖normalGraph n g y‖ < 1 / 4 :=
    (hsize y hy.1).trans (by linarith)
  have hDU (y : Plane) (hy : y ∈ D) : F y ∈ Metric.ball a (r / 2) := by
    change dist (a + quotientMap (normalGraph n g y)) a < r / 2
    rw [dist_eq_norm, add_sub_cancel_left, ← norm_shortestLift,
      shortestLift_quotientMap ((hsmall y hy).trans (by norm_num))]
    exact hsize y hy.1
  have hgd := hgood μ hμ N hN hp hn n hnorm g K hg hK a D hD hsmall
    (fun y hy ↦ hy.2) (Metric.ball a (r / 2)) measurableSet_ball hDU
  have hlo : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c * ρ ^ 2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball x ρ) := by
    rw [show frontier U = volumeSupport E ∩ volumeSupport Eᶜ from
      isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact hl μ hμ
  have hmH := trapped_graph_holes_volume_le (isOpen_openRepresentative E)
    (spatialNormalMeasure μ) hR hc hlo a hnorm hr hrs hε htrap S g hS
  have hbound (y : Plane) : ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ≤ 1 := by
    have hb : ‖fderiv ℝ g y‖ ≤ 1 := (norm_fderiv_le_of_lipschitz ℝ hg).trans (by exact_mod_cast hK)
    have hs : ‖fderiv ℝ g y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (fderiv ℝ g y)]
    simpa using ENNReal.ofReal_le_ofReal hs
  have heH : (∫⁻ y in H, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤
      C₁ * (spatialNormalMeasure μ : Measure Torus)
        ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
    apply (lintegral_mono hbound).trans
    simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using hmH
  have hsum : Ω = D ∪ H := by
    ext y
    simp only [D, H, mem_union, Set.mem_ofPred_eq]
    tauto
  change (∫⁻ y in Ω, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤ _
  calc
    _ ≤ (∫⁻ y in D, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) +
        ∫⁻ y in H, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane) := by
      rw [hsum]
      exact lintegral_union_le _ _ _
    _ ≤ C₀ * (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
        C₁ * (spatialNormalMeasure μ : Measure Torus)
          ((frontier U ∩ Metric.ball a (r / 2)) \ S) := add_le_add hgd heH
    _ ≤ C * (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
        C * (spatialNormalMeasure μ : Measure Torus)
          ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
      gcongr
      · exact le_self_add
      · exact le_add_self
    _ = _ := (mul_add _ _ _).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_coordinates {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v) = normalPlaneProjection n v := by
  have h := normalPlaneCoordinates_reconstruct hn v
  rw [normalPlaneProjection]
  exact eq_sub_iff_add_eq.mpr h

lemma good_cone_column_unique {B : Set Torus} {a c : Torus} {n : Cover}
    (hn : ‖n‖ = 1) {ρ ε : ℝ} (hρsmall : ρ < 1 / 2) (hε : ε ≤ 1 / 2)
    (hc : c ∈ Metric.ball a (ρ / 2))
    (hcone : ∀ x ∈ B, dist x c ≤ ρ → |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c)
    {x : Torus} (hx : x ∈ B ∩ Metric.ball a (ρ / 2))
    (hproj : normalPlaneCoordinates n (shortestLift (x - a)) =
      normalPlaneCoordinates n (shortestLift (c - a))) : x = c := by
  have hdist : dist x c ≤ ρ := by
    have hh := dist_triangle_right x c a
    change dist c a < ρ / 2 at hc
    have hx' : dist x a < ρ / 2 := hx.2
    linarith
  have hlocal : dist x a + dist c a < 1 / 2 := by
    have hx' : dist x a < ρ / 2 := hx.2
    change dist c a < ρ / 2 at hc
    linarith
  have hproj' : normalPlaneProjection n (shortestLift (x - c)) = 0 := by
    rw [shortestLift_sub_local hlocal, normalPlaneProjection_sub,
      ← normalPlaneEmbedding_coordinates hn, ← normalPlaneEmbedding_coordinates hn, hproj, sub_self]
  have hb := norm_le_two_normalPlaneProjection (v := shortestLift (x - c)) hn hε (by
    simpa only [norm_shortestLift, ← dist_eq_norm] using hcone x hx.1 hdist)
  rw [hproj', norm_zero, mul_zero, norm_shortestLift, ← dist_eq_norm] at hb
  exact dist_eq_zero.mp (le_antisymm hb dist_nonneg)

lemma phases_of_unique_frontier {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : ℝ → X} (hf : Continuous f)
    {s t q : ℝ} (hs : f s ∈ U) (ht : f t ∉ closure U)
    (huniq : ∀ u ∈ Icc s t, f u ∈ frontier U → u = q) :
    (∀ u ∈ Icc s t, u < q → f u ∈ U) ∧
      (∀ u ∈ Icc s t, q < u → f u ∉ closure U) := by
  constructor
  · intro u hu huq
    by_contra hnot
    by_cases hcl : f u ∈ closure U
    · have hbd : f u ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hcl, hnot⟩
      exact (ne_of_lt huq) (huniq u hu hbd)
    · obtain ⟨v, hv, hb⟩ := exists_frontier_on_interval hU hf hu.1 hs hcl
      have hveq := huniq v ⟨hv.1, hv.2.trans hu.2⟩ hb
      linarith [hv.2]
  · intro u hu hqu hcl
    by_cases hmem : f u ∈ U
    · obtain ⟨v, hv, hb⟩ := exists_frontier_on_interval hU hf hu.2 hmem ht
      have hveq := huniq v ⟨hu.1.trans hv.1, hv.2⟩ hb
      linarith [hv.1]
    · have hbd : f u ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hcl, hmem⟩
      exact (ne_of_gt hqu) (huniq u hu hbd)

theorem trapped_good_column_phases {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r ε η : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (hη : η ≤ 1 / 2)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r / 2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c - a)) ∈ Metric.ball (0 : Plane) (r / 4)) :
    let y := normalPlaneCoordinates n (shortestLift (c - a))
    let q := ⟪n, shortestLift (c - a)⟫
    (∀ t ∈ Icc (-r / 4) (r / 4), t < q →
      a + quotientMap (normalPlaneEmbedding n y + t • n) ∈ U) ∧
    (∀ t ∈ Icc (-r / 4) (r / 4), q < t →
      a + quotientMap (normalPlaneEmbedding n y + t • n) ∉ closure U) := by
  dsimp only
  let y := normalPlaneCoordinates n (shortestLift (c - a))
  let f : ℝ → Torus := fun t ↦ a + quotientMap (normalPlaneEmbedding n y + t • n)
  have hf : Continuous f := continuous_const.add
    (continuous_quotientMap.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hyn : ‖y‖ < r / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hsize (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ‖normalPlaneEmbedding n y + t • n‖ < r / 2 := by
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    have hab : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  have hl (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      shortestLift (f t - a) = normalPlaneEmbedding n y + t • n := by
    dsimp [f]
    rw [add_sub_cancel_left]
    exact shortestLift_quotientMap ((hsize t ht).trans (by linarith))
  have hd (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) : dist (f t) a < r / 2 := by
    rw [dist_eq_norm, ← norm_shortestLift, hl t ht]
    exact hsize t ht
  have hh (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ⟪n, shortestLift (f t - a)⟫ = t := by
    rw [hl t ht, inner_add_right, normalPlaneEmbedding_inner hn, inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have hlo : (-r / 4 : ℝ) ∈ Icc (-r / 4) (r / 4) := ⟨le_rfl, by linarith⟩
  have hhi : (r / 4 : ℝ) ∈ Icc (-r / 4) (r / 4) := ⟨by linarith, le_rfl⟩
  have hstart : f (-r / 4) ∈ U := htrap.2 ⟨(hd _ hlo).trans (by linarith), by
    rw [inner_neg_left, hh _ hlo]
    nlinarith⟩
  have hend : f (r / 4) ∉ closure U := htrap.1 ⟨(hd _ hhi).trans (by linarith), by
    rw [hh _ hhi]
    nlinarith⟩
  apply phases_of_unique_frontier hU hf hstart hend
  intro t ht hb
  have heq : f t = c := good_cone_column_unique hn hrsmall hη hc.2 hcone
    ⟨hb, hd t ht⟩ (by
      rw [hl t ht, map_add, map_smul, normalPlaneCoordinates_embedding,
        normalPlaneCoordinates_normal hn, smul_zero, add_zero])
  rw [← heq, hh t ht]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
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

lemma trapped_frontier_torus_height {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} {r ε : ℝ}
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a r) :
    |⟪n, shortestLift (c - a)⟫| ≤ ε * r := by
  apply abs_le.mpr
  constructor
  · by_contra! hh
    have hmem := htrap.2 (show c ∈ normalCap a (-n) r (ε * r) from
      ⟨hc.2, by rw [inner_neg_left]; linarith⟩)
    have hb := hc.1
    rw [frontier, hU.interior_eq] at hb
    exact hb.2 hmem
  · by_contra! hh
    exact htrap.1 ⟨hc.2, hh⟩ (frontier_subset_closure hc.1)

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

lemma good_column_characteristic {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (α*r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r/2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c-a)) ∈ Metric.ball (0 : Plane) (r/4))
    {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    characteristic U (a+quotientMap (normalPlaneEmbedding n
      (normalPlaneCoordinates n (shortestLift (c-a)))+t • n)) =
      columnPhase ⟪n, shortestLift (c-a)⟫ t := by
  have hp := trapped_good_column_phases hU hn hr hrs hα hη htrap hc hcone hy
  by_cases hlt : t < ⟪n, shortestLift (c-a)⟫
  · have hm := hp.1 t ht hlt
    simp [characteristic, columnPhase, hm, hlt]
  · have hm : a+quotientMap (normalPlaneEmbedding n
        (normalPlaneCoordinates n (shortestLift (c-a)))+t • n) ∉ U := by
      rcases lt_or_eq_of_le (le_of_not_gt hlt) with hgt | he
      · exact fun h ↦ hp.2 t ht hgt (subset_closure h)
      · rw [← he, normalPlaneCoordinates_reconstruct hn, quotientMap_shortestLift, add_sub_cancel]
        have hh := hc.1
        rw [frontier, hU.interior_eq] at hh
        exact hh.2
    simp [characteristic, columnPhase, hm, hlt]

lemma columnGraphMismatch_eq_zero_good {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (α*r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r/2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c-a)) ∈ Metric.ball (0 : Plane) (r/4))
    (g : Plane → ℝ) (he : g (normalPlaneCoordinates n (shortestLift (c-a))) =
      ⟪n, shortestLift (c-a)⟫) :
    columnGraphMismatch U a n r g (normalPlaneCoordinates n (shortestLift (c-a))) = 0 := by
  unfold columnGraphMismatch
  rw [he]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [good_column_characteristic hU hn hr hrs hα hη htrap hc hcone hy ht, sub_self, abs_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma small_column_lift (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hrs : r < 1/2) {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4))
    {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a) =
      normalPlaneEmbedding n y+t • n ∧
      dist (a+quotientMap (normalPlaneEmbedding n y+t • n)) a < r/2 := by
  have hy' : ‖y‖ < r/4 := by simpa only [mem_ball, dist_zero_right] using hy
  have hab : |t| ≤ r/4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hnorm : ‖normalPlaneEmbedding n y+t • n‖ < r/2 := by
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    linarith
  have hl : shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a) =
      normalPlaneEmbedding n y+t • n := by
    rw [add_sub_cancel_left]
    exact shortestLift_quotientMap (hnorm.trans (by linarith))
  exact ⟨hl, by rw [dist_eq_norm, ← norm_shortestLift, hl]; exact hnorm⟩

lemma trapped_column_phases {U : Set Torus} {a : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hrs : r < 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4)) {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    (t < -(α*r) → a+quotientMap (normalPlaneEmbedding n y+t • n) ∈ U) ∧
      (α*r < t → a+quotientMap (normalPlaneEmbedding n y+t • n) ∉ closure U) := by
  have hh := small_column_lift a hn hrs hy ht
  have hh' : ⟪n, shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a)⟫ = t := by
    rw [hh.1, inner_add_right, normalPlaneEmbedding_inner hn, inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  constructor
  · intro htlo
    apply htrap.2
    exact ⟨hh.2.trans (by linarith), by rw [inner_neg_left, hh']; linarith⟩
  · intro hthi
    exact htrap.1 ⟨hh.2.trans (by linarith), by rw [hh']; exact hthi⟩

lemma columnGraphMismatch_trapped_le {U : Set Torus} (hU : MeasurableSet U)
    {a : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα0 : 0 ≤ α) (hα : α < 1/4)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (g : Plane → ℝ) {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4))
    (hg : |g y| ≤ α*r) : columnGraphMismatch U a n r g y ≤ 2*α*r := by
  have hsub : Icc (-(α*r)) (α*r) ⊆ Icc (-r/4) (r/4) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hi : IntegrableOn ((Icc (-(α*r)) (α*r)).indicator (fun _ : ℝ ↦ (1 : ℝ)))
      (Icc (-r/4) (r/4)) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc
    _ ≤ ∫ t in Icc (-r/4) (r/4), (Icc (-(α*r)) (α*r)).indicator (fun _ : ℝ ↦ (1 : ℝ)) t := by
      apply integral_mono_ae (columnGraphMismatch_integrable hU a n r g y) hi
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      by_cases hs : t ∈ Icc (-(α*r)) (α*r)
      · rw [indicator_of_mem hs]
        exact columnPhase_difference_le U _ (g y) t
      · rw [indicator_of_notMem hs]
        have hp := trapped_column_phases hn hr hrs htrap hy ht
        simp only [mem_Icc, not_and_or, not_le] at hs
        rcases hs with hlo | hhi
        · have hu := hp.1 hlo
          have hlt : t < g y := hlo.trans_le (abs_le.mp hg).1
          simp [characteristic, columnPhase, hu, hlt]
        · have hu : a+quotientMap (normalPlaneEmbedding n y+t • n) ∉ U :=
            fun h ↦ hp.2 hhi (subset_closure h)
          have hlt : ¬ t < g y := not_lt.mpr ((abs_le.mp hg).2.trans hhi.le)
          simp [characteristic, columnPhase, hu, hlt]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
        integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, ENNReal.toReal_ofReal (by nlinarith [mul_nonneg hα0 hr.le] : 0 ≤ α*r - -(α*r))]
      ring

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma columnGraphMismatch_disagreement_volume_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀*ρ^2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x-a))) = ⟪n, shortestLift (x-a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c) :
    (volume : Measure Plane) {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0} ≤
      ((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c₀)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r/2)) \ S) := by
  let Q : Torus → Plane := fun x ↦ normalPlaneCoordinates n (shortestLift (x-a))
  have hs : {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0} ⊆
      Q '' ((frontier U ∩ Metric.ball a (r/2)) \ S) := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := trapped_boundary_projects_disk hU a hn hr hrs hα htrap hy.1
    have hxS : x ∉ S := by
      intro hm
      apply hy.2
      rw [← hxy]
      exact columnGraphMismatch_eq_zero_good hU hn hr hrs hα hη htrap hx (hcone x hm)
        (by simpa only [hxy] using hy.1) g (hS x hm)
    exact ⟨x, ⟨hx,hxS⟩, hxy⟩
  apply (measure_mono hs).trans
  apply plane_projection_volume_le_perimeter σ (frontier U) hR hc₀ hl n a _ (fun x hx ↦ hx.1.1)
  intro x hx
  exact (Metric.ball_subset_ball (by linarith : r/2 ≤ 1/4)) hx.1.2

theorem columnGraphMismatch_L1_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀*ρ^2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα0 : 0 ≤ α) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ) (hg : Measurable g)
    (hheight : ∀ y ∈ Metric.ball (0 : Plane) (r/4), |g y| ≤ α*r)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x-a))) = ⟪n, shortestLift (x-a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c) :
    (∫⁻ y in Metric.ball (0 : Plane) (r/4), ENNReal.ofReal (columnGraphMismatch U a n r g y)) ≤
      ENNReal.ofReal (2*α*r) * (((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c₀)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r/2)) \ S)) := by
  let D : Set Plane := {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0}
  have hD : MeasurableSet D := measurableSet_ball.inter
    (measurableSet_eq_fun (measurable_columnGraphMismatch hU.measurableSet a n r hg) measurable_const).compl
  have hb : ∀ y ∈ Metric.ball (0 : Plane) (r/4), ENNReal.ofReal (columnGraphMismatch U a n r g y) ≤
      D.indicator (fun _ ↦ ENNReal.ofReal (2*α*r)) y := by
    intro y hy
    by_cases he : columnGraphMismatch U a n r g y = 0
    · simp [he]
    · rw [indicator_of_mem (show y ∈ D from ⟨hy,he⟩)]
      exact ENNReal.ofReal_le_ofReal (columnGraphMismatch_trapped_le hU.measurableSet hn hr hrs hα0 hα htrap g hy (hheight y hy))
  calc
    _ ≤ ∫⁻ y in Metric.ball (0 : Plane) (r/4), D.indicator (fun _ ↦ ENNReal.ofReal (2*α*r)) y :=
      setLIntegral_mono' measurableSet_ball hb
    _ = ENNReal.ofReal (2*α*r) * (volume : Measure Plane) D := by
      rw [lintegral_indicator hD, lintegral_const, Measure.restrict_restrict hD]
      simp only [Measure.restrict_apply_univ, inter_eq_left.mpr (show D ⊆ Metric.ball (0 : Plane) (r/4) from fun _ h ↦ h.1)]
    _ ≤ _ := mul_le_mul_right (columnGraphMismatch_disagreement_volume_le hU σ hR hc₀ hl a hn hr hrs hα hη htrap S g hS hcone) _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma clamp_height_bound (f : Plane → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Plane) :
    |max (-r) (min r (f x))| ≤ r := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_tightly_trapped_graph_approximation_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ r₀ : ℝ, ∃ C : ℝ≥0∞, 0 < r₀ ∧ C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ r α : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1 / 4 →
        (normalCap a n r (α * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (α * r) ⊆ openRepresentative E) →
      ∃ (S : Set Torus) (g : Plane → ℝ),
        LipschitzWith ⟨2 * η, by positivity⟩ g ∧
        (∀ y, |g y| ≤ α * r) ∧
        S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (r / 2) ∧
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ r →
          |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) ∧
        let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
          ∂(spatialNormalMeasure μ : Measure Torus))
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4), ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2)) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
          ENNReal.ofReal (columnGraphMismatch (openRepresentative E) a n r g y)) ≤
            C * ENNReal.ofReal α * ENNReal.ofReal r * e := by
  obtain ⟨r₁, C₁, hr₁, hC₁, happ⟩ := isMinimizerAt_lipschitz_approximation_with_cones hV hE hmin hη hηhalf
  obtain ⟨C₂, hC₂, henergy⟩ := isMinimizerAt_normalGraph_full_energy hV hE hmin
  obtain ⟨R, c, hR, hc, hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let A : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)
  let C : ℝ≥0∞ := max (ENNReal.ofReal C₁) (max (C₂ * (1 + ENNReal.ofReal C₁)) (2 * A * ENNReal.ofReal C₁))
  have hCt : C < ⊤ := by dsimp [C, A]; finiteness
  have hCbad : ENNReal.ofReal C₁ ≤ C := le_max_left _ _
  have hCgrad : C₂ * (1 + ENNReal.ofReal C₁) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCheight : 2 * A * ENNReal.ofReal C₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min r₁ (1 / 4), C, by positivity, hCt, ?_⟩
  intro μ hμ N hN hp hn a n hnorm r α hr hrr hα0 hα htrap
  have hrs : r < 1 / 2 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S, hS, hbad, hcone, g₀, hg₀, heq₀⟩ := happ μ hμ N hN hp hn a n hnorm r hr
    (hrr.trans (min_le_left _ _))
  let K : NNReal := ⟨2 * η, by positivity⟩
  have hg₀x : LipschitzWith K g₀ := hg₀
  let g₁ : Plane → ℝ := fun y ↦ g₀ (normalPlaneEmbedding n y)
  have hg₁ : LipschitzWith K g₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdist : dist (normalPlaneEmbedding n x) (normalPlaneEmbedding n y) = dist x y := by
      simp only [dist_eq_norm]
      change ‖(normalPlaneLinearIsometry n) x - (normalPlaneLinearIsometry n) y‖ = ‖x - y‖
      rw [← map_sub, (normalPlaneLinearIsometry n).norm_map]
    exact (hg₀x.dist_le_mul (normalPlaneEmbedding n x) (normalPlaneEmbedding n y)).trans_eq
      (congrArg (fun t : ℝ ↦ (K : ℝ) * t) hdist)
  let g : Plane → ℝ := fun y ↦ max (-(α*r)) (min (α*r) (g₁ y))
  have hg : LipschitzWith ⟨2 * η, by positivity⟩ g := (hg₁.const_min (α*r)).const_max (-(α*r))
  have hheight (y : Plane) : |g y| ≤ α*r := clamp_height_bound g₁ (by positivity) y
  have heq (x : Torus) (hx : x ∈ S) : g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫ := by
    have hh := trapped_frontier_torus_height (isOpen_openRepresentative E) htrap
      ⟨(hS hx).1, (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) (hS hx).2⟩
    have hb : |⟪n, shortestLift (x - a)⟫| ≤ α*r := hh
    dsimp [g, g₁]
    rw [normalPlaneEmbedding_coordinates hnorm, heq₀ x hx,
      min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
    ∂(spatialNormalMeasure μ : Measure Torus))
  have hbad' : (spatialNormalMeasure μ : Measure Torus)
      ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ ENNReal.ofReal C₁ * e := hbad
  have hlocal : (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ e := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_sq_norm_sub_normal hN hn n).integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono_measure
      (Measure.restrict_mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ 17 * r))) le_rfl)
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (integrable_sq_norm_sub_normal hN hn n).integrableOn
  have he := henergy μ hμ N hN hp hn n hnorm g ⟨2 * η, by positivity⟩ hg
    (by exact_mod_cast (show 2 * η ≤ 1 by linarith)) a r α hr hrs hα htrap
    (fun y _ ↦ (hheight y).trans (by nlinarith)) S heq
  have hh := columnGraphMismatch_L1_le (isOpen_openRepresentative E)
    (spatialNormalMeasure μ) hR hc
    (by rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]; exact hlower μ hμ)
    a hnorm hr hrs hα0 hα hηhalf htrap S g hg.continuous.measurable (fun y _ ↦ hheight y) heq hcone
  refine ⟨S, g, hg, hheight, hS, heq, hcone, hbad'.trans (mul_le_mul_left hCbad _), ?_, ?_⟩
  · calc
      _ ≤ C₂ * (e + ENNReal.ofReal C₁ * e) := he.trans (mul_le_mul_right (add_le_add hlocal hbad') _)
      _ = (C₂ * (1 + ENNReal.ofReal C₁)) * e := by simp only [mul_add, add_mul, mul_one, mul_assoc]
      _ ≤ C * e := mul_le_mul_left hCgrad _
  · calc
      _ ≤ ENNReal.ofReal (2*α*r) * (A * (ENNReal.ofReal C₁ * e)) :=
        hh.trans (mul_le_mul_right (mul_le_mul_right hbad' A) _)
      _ = (2 * A * ENNReal.ofReal C₁) * ENNReal.ofReal α * ENNReal.ofReal r * e := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*α), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ac_rfl
      _ ≤ C * ENNReal.ofReal α * ENNReal.ofReal r * e :=
        mul_le_mul_left (mul_le_mul_left (mul_le_mul_left hCheight _) _) _

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation_oai := @OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation_oai
