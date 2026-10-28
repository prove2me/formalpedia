-- Prove2me | solution 1 for OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:25:57.635565+00:00
-- url     : https://prove2.me/submissions/64d62f0a-7e66-45b4-ac98-570c1f070987

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section
-- module Solutions.OAIQ3_Hot.HotSpots_Reciprocal
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section SingularLayer






open Filter
open scoped Topology
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_left (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    (1 - A) * resolvent A = 1 := mul_neg_geom_series A hA

lemma resolvent_right (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    resolvent A * (1 - A) = 1 := geom_series_mul_neg A hA

omit [CompleteSpace E] in
lemma resolvent_norm_le (A : E →L[ℝ] E) {d : ℝ} (hA : ‖A‖ ≤ d) (hd : d < 1) :
    ‖resolvent A‖ ≤ (1 - d)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one A (hA.trans_lt hd)
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hi : (1 - ‖A‖)⁻¹ ≤ (1 - d)⁻¹ := by
    apply inv_anti₀ (sub_pos.mpr hd)
    linarith
  dsimp only [resolvent]
  linarith

lemma resolvent_identity (A B : E →L[ℝ] E) (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    resolvent B - resolvent A = resolvent B * (B - A) * resolvent A := by
  have ht : B - A = (1 - A) - (1 - B) := by abel
  rw [ht, mul_sub, sub_mul, mul_assoc, resolvent_left A hA,
    resolvent_right B hB, mul_one, one_mul]

lemma resolvent_strong_tendsto (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v))) (v : E) :
    Tendsto (fun n => resolvent (Q n) v) atTop (𝓝 (resolvent A v)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hz : Tendsto (fun n => (1 - d)⁻¹ * ‖(Q n - A) (resolvent A v)‖) atTop (𝓝 0) := by
    have ht := ((hs (resolvent A v)).sub (tendsto_const_nhds (x := A (resolvent A v)))).norm.const_mul (1 - d)⁻¹
    simpa using ht
  apply squeeze_zero_norm' _ hz
  filter_upwards [hQ] with n hn
  have he := congrArg (fun T : E →L[ℝ] E => T v)
    (resolvent_identity A (Q n) hA (hn.trans_lt hd))
  simp only [sub_apply, mul_apply_eq_comp] at he
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))

lemma resolvent_solution (A : E →L[ℝ] E) (hA : ‖A‖ < 1) {u f : E}
    (hu : u - A u = f) : u = resolvent A f := by
  have h := congrArg (fun T : E →L[ℝ] E => T u) (resolvent_right A hA)
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, hu] using h.symm

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal




open MeasureTheory Filter
open scoped Topology ENNReal

namespace StrictHotSpots.BanachResolvent
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_strong_tendsto_moving (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => resolvent (Q n) (v n)) atTop (𝓝 (resolvent A w)) := by
  have hz : Tendsto (fun n => resolvent (Q n) (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => (1-d)⁻¹ * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul (1-d)⁻¹
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))
  have ht := hz.add (resolvent_strong_tendsto A Q hd hA hQ hs w)
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end StrictHotSpots.BanachResolvent

end SingularLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots


lemma existsUnique_of_coercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B u v = ℓ v := by
  let e := hB.continuousLinearEquivOfBilin
  let y := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨e.symm y, ?_, ?_⟩
  · intro v
    calc
      B (e.symm y) v = inner ℝ (e (e.symm y)) v :=
        (hB.continuousLinearEquivOfBilin_apply _ _).symm
      _ = ℓ v := by simp [y, InnerProductSpace.toDual_symm_apply]
  · intro u hu
    apply e.injective
    rw [e.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    calc
      inner ℝ (e u) v = B u v := hB.continuousLinearEquivOfBilin_apply _ _
      _ = ℓ v := hu v
      _ = inner ℝ y v := InnerProductSpace.toDual_symm_apply.symm




namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)



lemma existsUnique_energy_solution (hb : Bornology.IsBounded Ω)
    (ℓ : H10 hΩ →L[ℝ] ℝ) :
    ∃! u : H10 hΩ, ∀ v : H10 hΩ, energy hΩ u v = ℓ v := by
  exact @existsUnique_of_coercive (H10 hΩ) (H10.normedAddCommGroup hΩ)
    (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    (energy hΩ) (energy_coercive hΩ hb) ℓ


end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
namespace StrictHotSpots.DiskCutoff

lemma transition_deriv_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    simpa using h.deriv_eq
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    simpa using h.deriv_eq

lemma transition_deriv_bound : ∃ L : ℝ, 0 ≤ L ∧
    ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1) from
      (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp) |>.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have h : t < 0 ∨ 1 < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
    rw [transition_deriv_zero h, norm_zero]
    exact le_max_right _ _

variable {E : Type*} [NormedAddCommGroup E]

lemma cutoff_nonneg (κ : ℝ) (x : E) : 0 ≤ cutoff κ x :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (κ : ℝ) (x : E) : cutoff κ x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma cutoff_zero {κ : ℝ} {x : E} (hκ : 0 < κ) (hx : 1 - κ⁻¹ ≤ ‖x‖ ^ 2) :
    cutoff κ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx)]

lemma cutoff_one {κ : ℝ} {x : E} (hx : 2 ≤ κ * (1 - ‖x‖ ^ 2)) :
    cutoff κ x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma cutoff_tsupport {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ {x | ‖x‖ ^ 2 ≤ 1 - κ⁻¹} := by
  apply closure_minimal _ (isClosed_le (continuous_norm.pow 2) continuous_const)
  intro x hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹
  by_contra hh
  exact hx (cutoff_zero hκ (le_of_lt (lt_of_not_ge hh)))

lemma cutoff_tsupport_disk {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ Metric.ball 0 1 := by
  intro x hx
  have h := cutoff_tsupport hκ hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹ at h
  simp only [Metric.mem_ball, dist_zero_right]
  have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hn := norm_nonneg x
  nlinarith

lemma cutoff_hasCompactSupport [ProperSpace E] {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (cutoff (E := E) κ) :=
  isCompact_closedBall 0 1 |>.of_isClosed_subset (isClosed_tsupport _)
    ((cutoff_tsupport_disk hκ).trans Metric.ball_subset_closedBall)

variable [InnerProductSpace ℝ E]

lemma cutoff_contDiff (κ : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) κ) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_const.sub (contDiff_id.norm_sq (𝕜 := ℝ)))).sub contDiff_const)

lemma cutoff_fderiv (κ : ℝ) (x : E) :
    fderiv ℝ (cutoff κ) x =
      (-2 * κ * deriv Real.smoothTransition (κ * (1 - ‖x‖ ^ 2) - 1)) • innerSL ℝ x := by
  have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have ha := ((hnorm.const_sub 1).const_mul κ).sub_const 1
  have hb := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (κ * (1 - ‖x‖ ^ 2) - 1)).hasDerivAt
  have hc := hb.comp_hasFDerivAt x ha
  change fderiv ℝ (Real.smoothTransition ∘ fun x : E => κ * (1 - ‖x‖ ^ 2) - 1) x = _
  rw [hc.fderiv]
  ext y
  simp
  ring

lemma cutoff_fderiv_zero {κ : ℝ} {x : E}
    (hx : 2 < κ * (1 - ‖x‖ ^ 2)) : fderiv ℝ (cutoff κ) x = 0 := by
  rw [cutoff_fderiv, transition_deriv_zero (Or.inr (by linarith))]
  simp

lemma cutoff_eventually_one (x : E) (hx : ‖x‖ < 1) :
    ∀ᶠ n : ℕ in atTop, cutoff ((n : ℝ) + 2) x = 1 ∧
      fderiv ℝ (cutoff ((n : ℝ) + 2)) x = 0 := by
  have hp : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 2) * (1 - ‖x‖ ^ 2)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).atTop_mul_const hp
  filter_upwards [ht.eventually (eventually_gt_atTop (2 : ℝ))] with n hn
  exact ⟨cutoff_one hn.le, cutoff_fderiv_zero hn⟩

lemma boundary_vanishing_estimate [Nontrivial E] {f : E → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ x ∈ Metric.closedBall (0 : E) 1, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Metric.closedBall (0 : E) 1, ‖fderiv ℝ f x‖ ≤ C)
    (hz : ∀ x : E, ‖x‖ = 1 → f x = 0) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
  have hpoint : ∃ y : E, ‖y‖ = 1 ∧ ‖y-x‖ = 1-‖x‖ := by
    by_cases h : x = 0
    · obtain ⟨y,hy⟩ := exists_ne (0 : E)
      exact ⟨normalize y, norm_normalize hy, by simp [h, norm_normalize hy]⟩
    · refine ⟨normalize x, norm_normalize h, ?_⟩
      calc
        ‖normalize x - x‖ = ‖(1-‖x‖) • normalize x‖ := by rw [sub_smul, one_smul, norm_smul_normalize]
        _ = 1-‖x‖ := by rw [norm_smul, norm_normalize h, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)]
  obtain ⟨y,hy,hdist⟩ := hpoint
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hf hd
    (convex_closedBall (0 : E) (1 : ℝ))
    (show x ∈ Metric.closedBall (0 : E) 1 by simpa using hx)
    (show y ∈ Metric.closedBall (0 : E) 1 by simp [hy])
  rw [hz y hy, zero_sub, norm_neg, hdist] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [norm_nonneg x]

lemma cutoff_mul_contDiff {f : E → ℝ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) :
    ContDiff ℝ ∞ (fun x => cutoff κ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (cutoff (E := E) κ)
  · have hxd := cutoff_tsupport_disk hκ hx
    have hxR : x ∈ Metric.ball (0 : E) R := Metric.ball_subset_ball hR.le hxd
    exact (cutoff_contDiff κ).contDiffAt.mul
      ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR))
  · have he := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_hasCompactSupport [ProperSpace E] {f : E → ℝ} {κ : ℝ}
    (hκ : 0 < κ) : HasCompactSupport (fun x => cutoff κ x * f x) :=
  (cutoff_hasCompactSupport hκ).mul_right

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_norm_le {f : E → ℝ} {κ C : ℝ} {x : E} (hf : ‖f x‖ ≤ C) :
    ‖cutoff κ x * f x‖ ≤ C := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hf

lemma cutoff_mul_fderiv_bound {f : E → ℝ} {κ C L : ℝ} {x : E}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hx : ‖x‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hd : ‖fderiv ℝ f x‖ ≤ C)
    (hz : ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2))
    (ht : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) :
    ‖fderiv ℝ (fun x => cutoff κ x * f x) x‖ ≤ C + 4 * C * L := by
  rw [fderiv_fun_mul ((cutoff_contDiff κ).differentiable (by simp) x) hf]
  apply (norm_add_le _ _).trans
  have h1 : ‖cutoff κ x • fderiv ℝ f x‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hd
  have h2 : ‖f x • fderiv ℝ (cutoff κ) x‖ ≤ 4 * C * L := by
    by_cases hh : 2 < κ * (1 - ‖x‖ ^ 2)
    · rw [cutoff_fderiv_zero hh, smul_zero, norm_zero]
      positivity
    · have hh' : κ * (1 - ‖x‖ ^ 2) ≤ 2 := le_of_not_gt hh
      rw [norm_smul, cutoff_fderiv, norm_smul]
      simp only [norm_mul, norm_neg, Real.norm_of_nonneg hκ.le,
        innerSL_apply_norm]
      rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
      have hn : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      calc
        _ ≤ (C * (1 - ‖x‖ ^ 2)) * (2 * κ * L * 1) := by
          apply mul_le_mul hz _ (by positivity) (mul_nonneg hC hn)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (ht _) (by positivity)) hx
            (norm_nonneg _) (by positivity)
        _ = 2 * C * L * (κ * (1 - ‖x‖ ^ 2)) := by ring
        _ ≤ 4 * C * L := by nlinarith [mul_le_mul_of_nonneg_left hh' (show 0 ≤ 2 * C * L by positivity)]
  exact add_le_add h1 h2

end StrictHotSpots.DiskCutoff

namespace StrictHotSpots

namespace DiskH10
open DiskCutoff

lemma norm_gradient_eq (f : Plane → ℝ) (x : Plane) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma smooth_zero_boundary_bounds {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖fderiv ℝ f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2)) := by
  have hs : Metric.closedBall (0 : Plane) 1 ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hR
  have hdc := hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Plane) 1).exists_bound_of_continuousOn
    (hdc.mono hs)
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hd : ∀ x ∈ Metric.closedBall (0 : Plane) 1, ‖fderiv ℝ f x‖ ≤ C :=
    fun x hx => (hB x hx).trans (le_max_left _ _)
  have hdiff : ∀ x ∈ Metric.closedBall (0 : Plane) 1, DifferentiableAt ℝ f x :=
    fun x hx => ((hf x (hs hx)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hx))).differentiableAt (by simp)
  have hv : ∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
    intro x hx
    exact boundary_vanishing_estimate hC hdiff hd hz (by simpa [disk] using (Metric.ball_subset_closedBall hx))
  refine ⟨C,hC,?_,fun x hx => hd x (Metric.ball_subset_closedBall hx),hv⟩
  intro x hx
  exact (hv x hx).trans (by nlinarith [sq_nonneg ‖x‖, mul_nonneg hC (sq_nonneg ‖x‖)])



lemma smooth_zero_boundary_memH10 {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    (smooth_memH1 hR hf).toH1 ∈ h10Submodule (Ω := disk) Metric.isOpen_ball := by
  let hΩ : IsOpen disk := Metric.isOpen_ball
  let h := smooth_memH1 hR hf
  let : IsFiniteMeasure (volume.restrict disk) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  obtain ⟨C,hC,hv,hd,hzC⟩ := smooth_zero_boundary_bounds hR hf hz
  obtain ⟨L,hL,ht⟩ := transition_deriv_bound
  let ψ : ℕ → Plane → ℝ := fun n x => cutoff ((n : ℝ) + 2) x * f x
  have hκ (n : ℕ) : 0 < (n : ℝ) + 2 := by positivity
  have hψ (n : ℕ) : ContDiff ℝ ∞ (ψ n) := cutoff_mul_contDiff (hκ n) hR hf
  have hc (n : ℕ) : HasCompactSupport (ψ n) := cutoff_mul_hasCompactSupport (hκ n)
  have hs (n : ℕ) : tsupport (ψ n) ⊆ disk :=
    tsupport_mul_subset_left.trans (cutoff_tsupport_disk (hκ n))
  let test : ℕ → smoothTestSpace disk := fun n => ⟨ψ n, hψ n, hc n, hs n⟩
  have hdiff (x : Plane) (hx : x ∈ disk) : DifferentiableAt ℝ f x := by
    have hxR : x ∈ Metric.ball (0 : Plane) R := Metric.ball_subset_ball hR.le hx
    exact ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR)).differentiableAt (by simp)
  have hval : Tendsto (fun n => H1.value (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.value h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_memLp (hψ n) (hc n)) h.1 (memLp_const C)
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact cutoff_mul_norm_le (hv x hx)
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, ψ n x = f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        simp only [ψ, hn.1, one_mul]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  have hgrad : Tendsto (fun n => H1.grad (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.grad h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_gradient_memLp (hψ n) (hc n)) h.2.1 (memLp_const (C + 4 * C * L))
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [norm_gradient_eq]
      exact cutoff_mul_fderiv_bound (hκ n) hC hL
        (by simpa [disk] using (Metric.ball_subset_closedBall hx))
        (hdiff x hx) (hd x hx) (hzC x hx) ht
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, gradient (ψ n) x = gradient f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        unfold gradient ψ
        rw [fderiv_fun_mul ((cutoff_contDiff _).differentiable (by simp) x) (hdiff x hx)]
        simp only [hn.1, hn.2, one_smul, smul_zero, add_zero]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  change h.toH1 ∈ closure ((smoothTestToH1 hΩ).range : Set (H1 disk))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hval hgrad)
    (Eventually.of_forall fun n => ⟨test n, rfl⟩)

end DiskH10
end StrictHotSpots

open scoped Laplacian
namespace StrictHotSpots

lemma integral_inner_gradient_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient φ x)) =
      -(∫ x in Ω, Δ f x * φ x) := by
  let b := stdOrthonormalBasis ℝ Plane
  have hd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (b i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i)) Ω :=
    ((hd i).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have he (x : Plane) : inner ℝ (gradient f x) (gradient φ x) =
      ∑ i, fderiv ℝ f x (b i) * fderiv ℝ φ x (b i) := by
    rw [← b.sum_inner_mul_inner (gradient f x) (gradient φ x)]
    simp only [inner_gradient_left, inner_gradient_right, starRingEnd_apply, star_trivial]
  have hl (x : Plane) (hx : x ∈ Ω) : Δ f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    rw [fderiv_clm_apply
      ((((hf x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hi (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ f x (b i) * fderiv ℝ φ x (b i)) (volume.restrict Ω) := by
    apply Integrable.restrict
    exact integrable_mul_test hΩ (hd i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have hj (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hdd i).continuousOn hφ.continuous hc hs).restrict
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_test_fderiv hΩ (hd _) hφ hc hs]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hl x hx, Finset.sum_mul]

lemma inner_toLp_toLp {X F : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f g : X → F}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

lemma smoothTest_value {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.value (smoothTestToH1 hΩ φ) =
      (test_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (φ : Plane → ℝ) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.value_toH1]

lemma smoothTest_grad {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.grad (smoothTestToH1 hΩ φ) =
      (test_gradient_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (gradient (φ : Plane → ℝ)) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.grad_toH1]

lemma smooth_weak_poisson {Ω : Set Plane} {u f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (huH1 : HasH1Gradient Ω u (gradient u))
    (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ x ∈ Ω, Δ u x = -f x) (v : H10 hΩ) :
    inner ℝ (H1.grad huH1.toH1) (H10.grad hΩ v) =
      inner ℝ (hf.toLp f) (H10.value hΩ v) := by
  let S : Set (H1 Ω) := {w | inner ℝ (H1.grad huH1.toH1) (H1.grad w) =
    inner ℝ (hf.toLp f) (H1.value w)}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner H1.grad.continuous)
    (continuous_const.inner H1.value.continuous)
  have hi : ((smoothTestToH1 hΩ).range : Set (H1 Ω)) ⊆ S := by
    rintro w ⟨φ,rfl⟩
    change inner ℝ (H1.grad huH1.toH1) (H1.grad (smoothTestToH1 hΩ φ)) =
      inner ℝ (hf.toLp f) (H1.value (smoothTestToH1 hΩ φ))
    rw [H1.grad_toH1, smoothTest_grad, smoothTest_value, inner_toLp_toLp, inner_toLp_toLp,
      integral_inner_gradient_test hΩ hu φ.property.1 φ.property.2.1 φ.property.2.2]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hp x hx]
    ring
  exact (closure_minimal hi hS) v.property

end StrictHotSpots







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian

open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace

namespace StrictHotSpots.GreenFundamental

lemma denominator_pos {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    0 < ‖z‖ ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)

lemma logRegularized_contDiff {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (logRegularized ε) := by
  exact ((contDiff_id.norm_sq (𝕜 := ℂ)).add contDiff_const).log
    (fun z => (denominator_pos hε z).ne')

lemma logRegularized_fderiv {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    fderiv ℝ (logRegularized ε) z =
      (‖z‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ z) := by
  exact (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).log
    (denominator_pos hε z).ne').fderiv

lemma logRegularized_second {ε : ℝ} (hε : ε ≠ 0) (z a b : ℂ) :
    fderiv ℝ (fderiv ℝ (logRegularized ε)) z a b =
      2 * (‖z‖ ^ 2 + ε ^ 2)⁻¹ * ⟪a, b⟫_ℝ -
        4 * (‖z‖ ^ 2 + ε ^ 2)⁻¹ ^ 2 * ⟪z, a⟫_ℝ * ⟪z, b⟫_ℝ := by
  have hf : fderiv ℝ (logRegularized ε) = fun z : ℂ =>
      (‖z‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ z) :=
    funext (logRegularized_fderiv hε)
  rw [hf]
  have hd := (hasDerivAt_inv (denominator_pos hε z).ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2))
  have hi : HasFDerivAt (fun z : ℂ => 2 • innerSL ℝ z) (2 • innerSL ℝ (E := ℂ)) z := by
    exact (2 • innerSL ℝ (E := ℂ)).hasFDerivAt
  calc
    _ = _ := congrArg (fun L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) => L a b) (hd.smul hi).fderiv
    _ = _ := by
      simp only [add_apply, smul_apply, two_smul, ContinuousLinearMap.smulRight_apply,
        Function.comp_def, neg_mul, smul_eq_mul, innerSL_apply_apply]
      erw [innerSL_apply_apply]
      simp only [← inv_pow]
      ring

lemma logRegularized_laplacian {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    Δ (logRegularized ε) z = 4 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, logRegularized_second hε]
  have hz : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z
  simp only [Complex.inner]
  simp at *
  field_simp
  nlinarith

lemma radial_primitive_hasDerivAt (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(2 * Real.pi)⁻¹ * (1 + r ^ 2)⁻¹)
      (r / (Real.pi * (1 + r ^ 2)^2)) r := by
  have hd := ((hasDerivAt_id r).pow 2).const_add 1
  have h := (hasDerivAt_inv (show 1 + r ^ 2 ≠ 0 by positivity)).comp r hd
  have hh := h.const_mul (-(2 * Real.pi)⁻¹)
  simp only [Function.comp_def, id_eq, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one] at hh
  convert! hh using 1
  field_simp

lemma radial_primitive_tendsto :
    Tendsto (fun r : ℝ => -(2 * Real.pi)⁻¹ * (1 + r ^ 2)⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) (tendsto_pow_atTop two_ne_zero))).const_mul
      (-(2 * Real.pi)⁻¹)

lemma integral_radial :
    ∫ r in Ioi (0 : ℝ), r / (Real.pi * (1 + r ^ 2)^2) = (2 * Real.pi)⁻¹ := by
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (fun r _ => radial_primitive_hasDerivAt r)
    (fun r hr => div_nonneg hr.le (by positivity)) radial_primitive_tendsto

lemma integral_peak : ∫ z : ℂ, peak z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  have heq : (fun p : ℝ × ℝ => p.1 • peak (Complex.polarCoord.symm p)) =
      (fun p : ℝ × ℝ => (p.1 / (Real.pi * (1 + p.1 ^ 2)^2)) * (1 : ℝ)) := by
    funext p
    simp [peak, sq_abs, div_eq_mul_inv]
  rw [heq]
  change (∫ p in (Ioi (0 : ℝ)) ×ˢ Ioo (-Real.pi) Real.pi,
    (p.1 / (Real.pi * (1 + p.1 ^ 2)^2)) * (1 : ℝ)) = 1
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r / (Real.pi * (1 + r ^ 2)^2))
      (fun _ : ℝ => (1 : ℝ)), integral_radial]
  simp [Real.pi_pos.le]
  field_simp
  ring

lemma peak_nonneg (z : ℂ) : 0 ≤ peak z := by
  unfold peak
  positivity

lemma peak_decay : Tendsto (fun z : ℂ => ‖z‖ ^ Module.finrank ℝ ℂ * peak z)
    (cobounded ℂ) (𝓝 0) := by
  have h : Tendsto (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (1 : ℝ)
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop))
  have hh := (h.sub (h.pow 2)).const_mul Real.pi⁻¹
  simp only [zero_pow two_ne_zero, sub_zero, mul_zero] at hh
  convert! hh using 1
  funext z
  simp only [Complex.finrank_real_complex, peak]
  field_simp
  ring

lemma tendsto_peak_mul {φ : ℂ → ℝ} (hφ : Integrable φ) (hc : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, (c ^ 2 * peak (c • z)) * φ z)
      atTop (𝓝 (φ 0)) := by
  simpa only [Complex.finrank_real_complex, smul_eq_mul] using
    tendsto_integral_comp_smul_smul_of_integrable peak_nonneg integral_peak peak_decay hφ hc

lemma logRegularized_laplacian_scale {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    Δ (logRegularized c⁻¹) z = (4 * Real.pi) * (c ^ 2 * peak (c • z)) := by
  rw [logRegularized_laplacian (inv_ne_zero hc)]
  simp only [peak, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hd : ‖z‖ ^ 2 + c⁻¹ ^ 2 ≠ 0 := (denominator_pos (inv_ne_zero hc) z).ne'
  have hd' : 1 + c ^ 2 * ‖z‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma tendsto_logRegularized_laplacian_mul {φ : ℂ → ℝ}
    (hφ : Integrable φ) (hc : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, Δ (logRegularized c⁻¹) z * φ z)
      atTop (𝓝 ((4 * Real.pi) * φ 0)) := by
  apply ((tendsto_peak_mul hφ hc).const_mul (4 * Real.pi)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  simp_rw [logRegularized_laplacian_scale hc.ne', mul_assoc]
  simpa only [mul_assoc] using (integral_const_mul (μ := (volume : Measure ℂ)) (4 * Real.pi)
    (fun z : ℂ => c ^ 2 * (peak (c • z) * φ z))).symm

lemma direction_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (e : ℂ) :
    ContDiff ℝ ∞ (direction f e) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma direction_compact {φ : ℂ → ℝ} (hc : HasCompactSupport φ) (e : ℂ) :
    HasCompactSupport (direction φ e) := hc.fderiv_apply ℝ e

lemma second_direction {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (e x : ℂ) :
    direction (direction f e) e x = fderiv ℝ (fderiv ℝ f) x e e := by
  unfold direction
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const _)]
  simp

lemma laplacian_direction {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ f = fun x => direction (direction f 1) 1 x +
      direction (direction f Complex.I) Complex.I x := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, second_direction hf]

lemma integral_direction_by_parts {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, f x * direction φ e x = -(∫ x, direction f e x * φ x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((direction_smooth hf e).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  · exact (hf.continuous.mul (direction_smooth hφ e).continuous).integrable_of_hasCompactSupport
      (direction_compact hc e).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hφ.differentiable (by simp) x

lemma integral_second_direction {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, f x * direction (direction φ e) e x =
      ∫ x, direction (direction f e) e x * φ x := by
  rw [integral_direction_by_parts hf (direction_smooth hφ e) (direction_compact hc e),
    integral_direction_by_parts (direction_smooth hf e) hφ hc, neg_neg]

lemma integral_laplacian_by_parts {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, f x * Δ φ x = ∫ x, Δ f x * φ x := by
  have hi (e : ℂ) : Integrable (fun x => f x * direction (direction φ e) e x) :=
    (hf.continuous.mul (direction_smooth (direction_smooth hφ e) e).continuous).integrable_of_hasCompactSupport (direction_compact (direction_compact hc e) e).mul_left
  have hi' (e : ℂ) : Integrable (fun x => direction (direction f e) e x * φ x) :=
    ((direction_smooth (direction_smooth hf e) e).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  simp_rw [laplacian_direction hf, laplacian_direction hφ, mul_add, add_mul]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hi' 1) (hi' Complex.I),
    integral_second_direction hf hφ hc, integral_second_direction hf hφ hc]

lemma tendsto_logRegularized_test {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, logRegularized c⁻¹ z * Δ φ z)
      atTop (𝓝 ((4 * Real.pi) * φ 0)) := by
  apply (tendsto_logRegularized_laplacian_mul
    (hφ.continuous.integrable_of_hasCompactSupport hc) hφ.continuous.continuousAt).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc'
  exact (integral_laplacian_by_parts (logRegularized_contDiff (inv_ne_zero hc'.ne')) hφ hc).symm

lemma abs_log_bound {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + t⁻¹ := by
  have hu := Real.log_le_sub_one_of_pos ht
  have hl := Real.one_sub_inv_le_log_of_pos ht
  exact abs_le.mpr ⟨by linarith, by have := inv_pos.mpr ht; linarith⟩

lemma log_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := R ^ 2 + 1) (α := 1)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (1 : ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, Real.rpow_neg_one]
    by_cases he : z = 0
    · simp [he]
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr he
      have hr : ‖z‖ < R := by simpa using hz
      calc
        _ ≤ ‖z‖ + ‖z‖⁻¹ := abs_log_bound hp
        _ ≤ (R ^ 2 + 1) * ‖z‖⁻¹ := by
          rw [← div_eq_mul_inv]
          apply (le_div_iff₀ hp).mpr
          have he : (‖z‖ + ‖z‖⁻¹) * ‖z‖ = ‖z‖ ^ 2 + 1 := by field_simp
          rw [he]
          nlinarith
  · exact (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable

lemma logRegularized_abs_le {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    {z : ℂ} (hz : z ≠ 0) :
    |logRegularized ε z| ≤ 2 * |Real.log ‖z‖| + ‖z‖ ^ 2 + 1 := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hl := Real.log_le_log (sq_pos_of_pos hp) (le_add_of_nonneg_right (sq_nonneg ε))
  have hu := Real.log_le_self (show 0 ≤ ‖z‖ ^ 2 + ε ^ 2 by positivity)
  rw [Real.log_pow] at hl
  norm_num at hl
  have ha := neg_abs_le (Real.log ‖z‖)
  have hb := abs_nonneg (Real.log ‖z‖)
  unfold logRegularized
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg ‖z‖], by nlinarith⟩

lemma tendsto_logRegularized {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => logRegularized c⁻¹ z) atTop (𝓝 (2 * Real.log ‖z‖)) := by
  have hp : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have ht : Tendsto (fun c : ℝ => ‖z‖ ^ 2 + (c⁻¹) ^ 2) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa using (tendsto_const_nhds (x := ‖z‖ ^ 2)).add (tendsto_inv_atTop_zero.pow 2)
  simpa [logRegularized, Real.log_pow, Function.comp_def] using (Real.continuousAt_log hp).tendsto.comp ht

lemma tendsto_integral_logRegularized {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, logRegularized c⁻¹ z * ψ z)
      atTop (𝓝 (∫ z : ℂ, (2 * Real.log ‖z‖) * ψ z)) := by
  obtain ⟨R, hR, hsub⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  let bound : ℂ → ℝ := (Metric.ball (0 : ℂ) R).indicator
    (fun z => (2 * |Real.log ‖z‖| + R ^ 2 + 1) * B)
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_ball).mpr
    exact ((((log_norm_integrableOn_ball R).abs.const_mul 2).add
      (integrableOn_const (measure_ball_lt_top.ne))).add
      (integrableOn_const (measure_ball_lt_top.ne))).mul_const B
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hi ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc'
    exact ((logRegularized_contDiff (inv_ne_zero hc'.ne')).continuous.mul hψ).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (1 : ℝ)] with c hc'
    change 1 ≤ c at hc'
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    by_cases hzr : z ∈ Metric.ball (0 : ℂ) R
    · rw [norm_mul, Real.norm_eq_abs, show bound z =
        (2 * |Real.log ‖z‖| + R ^ 2 + 1) * B from Set.indicator_of_mem hzr _]
      have hr : ‖z‖ < R := by simpa using hzr
      have hli : |logRegularized c⁻¹ z| ≤ 2 * |Real.log ‖z‖| + R ^ 2 + 1 := by
        apply (logRegularized_abs_le (inv_nonneg.mpr (by linarith))
          (inv_le_one₀ (by linarith) |>.mpr hc') hz).trans
        nlinarith [norm_nonneg z]
      exact mul_le_mul hli (hB z) (norm_nonneg _) (by positivity)
    · have hzψ : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz' => hzr (hsub hz'))
      simp [hzψ, bound, hzr]
  · filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact (tendsto_logRegularized hz).mul_const (ψ z)

lemma laplacian_smooth {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Δ φ) := by
  rw [laplacian_direction hφ]
  exact (direction_smooth (direction_smooth hφ 1) 1).add
    (direction_smooth (direction_smooth hφ Complex.I) Complex.I)

lemma laplacian_compact {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (Δ φ) := by
  rw [laplacian_direction hφ]
  exact (direction_compact (direction_compact hc 1) 1).add
    (direction_compact (direction_compact hc Complex.I) Complex.I)



lemma integral_log_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z : ℂ, Real.log ‖z‖ * Δ φ z = (2 * Real.pi) * φ 0 := by
  have he := tendsto_nhds_unique (tendsto_logRegularized_test hφ hc)
    (tendsto_integral_logRegularized (laplacian_smooth hφ).continuous
      (laplacian_compact hφ hc))
  simp_rw [mul_assoc] at he
  rw [integral_const_mul] at he
  linarith

lemma log_norm_locallyIntegrable : LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) := by
  intro z
  refine ⟨Metric.ball (0 : ℂ) (‖z‖ + 1), Metric.isOpen_ball.mem_nhds ?_,
    log_norm_integrableOn_ball _⟩
  simp

lemma laplacian_comp_add_right (φ : ℂ → ℝ) (a : ℂ) :
    Δ (fun z => φ (z+a)) = fun z => Δ φ (z+a) := by
  funext z
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_comp_add_right]

lemma log_sub_mul_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (a : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z-a‖ * ψ z) := by
  have hi := log_norm_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    (hψ.comp (continuous_id.add continuous_const))
    (hc.comp_homeomorph (Homeomorph.addRight a))
  simpa [Function.comp_def, sub_eq_add_neg, smul_eq_mul] using
    (measurePreserving_add_right volume (-a)).integrable_comp_of_integrable hi

end StrictHotSpots.GreenFundamental

namespace StrictHotSpots.DiskFormula
open StrictHotSpots.GreenFundamental



lemma disk_cross_identity (x y : ℂ) :
    ‖1 - x * star y‖ ^ 2 = (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) + ‖x-y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma green_eq_log {x y : ℂ} (hxy : x ≠ y) (hnum : 1 - x * star y ≠ 0) :
    green x y = (Real.log ‖1-x*star y‖ - Real.log ‖x-y‖) / (2 * Real.pi) := by
  have hd := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hnum)
  have he : 1 + (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) / ‖x-y‖ ^ 2 =
      ‖1-x*star y‖ ^ 2 / ‖x-y‖ ^ 2 := by
    rw [disk_cross_identity, add_div, div_self hd]
    ring
  rw [green, he, Real.log_div hn hd, Real.log_pow, Real.log_pow]
  ring

end StrictHotSpots.DiskFormula

open scoped Convolution
namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental

lemma direction_convolution {f g : ℂ → ℝ}
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (e : ℂ) : direction (f ⋆ g) e = f ⋆ (direction g e) := by
  funext x
  rw [direction, (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (hg.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (hc.fderiv ℝ) (hg.continuous_fderiv (by simp)) x e

lemma laplacian_convolution {f g : ℂ → ℝ}
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Δ (f ⋆ g) = f ⋆ (Δ g) := by
  rw [laplacian_direction (hc.contDiff_convolution_right _ hf hg), laplacian_direction hg]
  rw [direction_convolution hf hg hc, direction_convolution hf hg hc,
    direction_convolution hf (direction_smooth hg _) (direction_compact hc _),
    direction_convolution hf (direction_smooth hg _) (direction_compact hc _)]
  funext x
  symm
  apply ConvolutionExistsAt.distrib_add
  · exact (direction_compact (direction_compact hc _) _).convolutionExists_right _ hf
      (direction_smooth (direction_smooth hg _) _).continuous x
  · exact (direction_compact (direction_compact hc _) _).convolutionExists_right _ hf
      (direction_smooth (direction_smooth hg _) _).continuous x



lemma log_potential_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ ((fun z : ℂ => Real.log ‖z‖) ⋆ f) :=
  hc.contDiff_convolution_right _ log_norm_locallyIntegrable hf

lemma laplacian_comp_neg {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    Δ (fun x : ℂ => f (-x)) z = Δ f (-z) := by
  have hh := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := 2) (-1 : ℝ)
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hh' : iteratedFDeriv ℝ 2 (fun x : ℂ => f (-x)) z =
      iteratedFDeriv ℝ 2 f (-z) := by
    simpa using congrFun hh z
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, hh']

lemma laplacian_comp_const_sub {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (a z : ℂ) :
    Δ (fun x : ℂ => f (a-x)) z = Δ f (a-z) := by
  have he : (fun x : ℂ => f (a-x)) = fun x => (fun y => f (y+a)) (-x) := by
    funext x; congr 1; abel
  have hshift : ContDiff ℝ ∞ (fun y : ℂ => f (y+a)) :=
    hf.comp (contDiff_id.add contDiff_const)
  calc
    _ = Δ (fun y : ℂ => f (y+a)) (-z) := by
      rw [he]
      exact laplacian_comp_neg hshift z
    _ = Δ f (-z+a) := congrFun (laplacian_comp_add_right f a) (-z)
    _ = Δ f (a-z) := by rw [sub_eq_add_neg, add_comm a]



lemma log_potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    Δ ((fun x : ℂ => Real.log ‖x‖) ⋆ f) z = (2 * Real.pi) * f z := by
  rw [laplacian_convolution log_norm_locallyIntegrable hf hc]
  let φ : ℂ → ℝ := fun x => f (z-x)
  have hφ : ContDiff ℝ ∞ φ := hf.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := by
    simpa [φ, Function.comp_def, sub_eq_add_neg, add_comm] using
      hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addRight z))
  have h := integral_log_laplacian hφ hφc
  simp only [φ, laplacian_comp_const_sub hf, sub_zero] at h
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

lemma correctionIntegrand_contDiffOn {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : Set ℂ} (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (correctionIntegrand f) (s ×ˢ univ) := by
  intro p hp
  by_cases hy : p.2 ∈ tsupport f
  · have hg : ContDiff ℝ ∞ (fun p : ℂ × ℂ => 1-p.1*star p.2) := by
      exact contDiff_const.sub (contDiff_fst.mul
        (Complex.conjCLE.contDiff.comp contDiff_snd))
    exact ((hf.comp contDiff_snd).contDiffAt.mul
      ((hg.contDiffAt.norm (𝕜 := ℂ) (hn p.1 hp.1 p.2 hy)).log
        (norm_ne_zero_iff.mpr (hn p.1 hp.1 p.2 hy)))).contDiffWithinAt
  · have he : (fun q : ℂ × ℂ => f q.2) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto continuousAt_snd
    have hz : ContDiffAt ℝ ∞ (correctionIntegrand f) p := by
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with q hq
      simp [correctionIntegrand, hq]
    exact hz.contDiffWithinAt

lemma correction_potential_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) s := by
  have hh := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : ℂ => (0 : ℂ))
    contDiffOn_const (f := fun _ : ℂ => (1 : ℝ))
    (g := fun z y => correctionIntegrand f (z,y)) hs hc.isCompact
    (fun z y _ hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
    (locallyIntegrable_const (μ := (volume : Measure ℂ)) (1 : ℝ))
    (correctionIntegrand_contDiffOn hf hn)
  simpa only [convolution_def, correctionIntegrand, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_one] using hh

end StrictHotSpots.GreenPotential



open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
namespace StrictHotSpots.CompactParameter

variable {s k : Set ℂ} {F : ℂ × ℂ → ℝ}

lemma fderiv_eq_zero_outside (hs : IsOpen s) (hk : IsClosed k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) {p : ℂ × ℂ}
    (hp : p.1 ∈ s) (hy : p.2 ∉ k) : fderiv ℝ F p = 0 := by
  have hd : HasFDerivAt F (0 : (ℂ × ℂ) →L[ℝ] ℝ) p := by
    apply (hasFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq
    filter_upwards [(hs.prod hk.isOpen_compl).mem_nhds (show p ∈ s ×ˢ kᶜ from ⟨hp,hy⟩)] with q hq
    exact hz q.1 hq.1 q.2 hq.2
  exact hd.fderiv

lemma fderiv_section_compact (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) {z : ℂ} (hzz : z ∈ s) :
    HasCompactSupport (fun y : ℂ => fderiv ℝ F (z,y)) := by
  apply HasCompactSupport.intro hk
  intro y hy
  exact fderiv_eq_zero_outside hs hk.isClosed hz hzz hy

lemma fderiv_section_continuous (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) :
    Continuous (fun y : ℂ => fderiv ℝ F (z,y)) := by
  exact (hf.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) (by simp)).comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨hz, mem_univ y⟩)

lemma hasFDerivAt_integral (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    HasFDerivAt (fun z : ℂ => ∫ y : ℂ, F (z,y))
      ((∫ y : ℂ, fderiv ℝ F (z,y)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) z := by
  have h := hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℂ))
    (f := fun _ : ℂ => (1 : ℝ)) (g := fun z y => F (z,y))
    hs hk (fun z y hzz hy => hz z hzz y hy)
    (locallyIntegrable_const (1 : ℝ)) (hf.of_le (by simp)) (z,0) hzz
  have h' := h.comp z (ContinuousLinearMap.inl ℝ ℂ ℂ).hasFDerivAt
  have hfun : (fun z : ℂ => (fun q : ℂ × ℂ =>
      ((fun _ : ℂ => (1 : ℝ)) ⋆ (fun y => F (q.1,y))) q.2)
      ((ContinuousLinearMap.inl ℝ ℂ ℂ) z)) =
      (fun z : ℂ => ∫ y : ℂ, F (z,y)) := by
    funext z
    simp only [ContinuousLinearMap.inl_apply, convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul, zero_sub]
    exact integral_neg_eq_self (fun y : ℂ => F (z,y)) volume
  simp only [Function.comp_def] at h'
  rw [hfun] at h'
  convert! h' using 1
  congr 1
  change (∫ y : ℂ, fderiv ℝ F (z,y)) =
    ∫ y : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℂ × ℂ) 1
      (fderiv ℝ F (z,0-y))
  have hid : (ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℂ × ℂ) 1 =
      ContinuousLinearMap.id ℝ ((ℂ × ℂ) →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro D
    apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.precompR_apply]
  rw [hid]
  simpa only [zero_sub, ContinuousLinearMap.id_apply] using
    (integral_neg_eq_self (fun y : ℂ => fderiv ℝ F (z,y)) volume).symm

lemma partial_contDiffOn (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) (e : ℂ) :
    ContDiffOn ℝ ∞ (paramDeriv F e) (s ×ˢ univ) :=
  (hf.fderiv_of_isOpen (hs.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

lemma partial_zero_outside (hs : IsOpen s) (hk : IsClosed k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) (e : ℂ) :
    ∀ z ∈ s, ∀ y ∉ k, paramDeriv F e (z,y) = 0 := by
  intro z hzz y hy
  simp [paramDeriv, fderiv_eq_zero_outside hs hk hz (p := (z,y)) hzz hy]

lemma integral_contDiffOn (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∫ y : ℂ, F (z,y)) s := by
  have hh := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : ℂ => (0 : ℂ))
    contDiffOn_const (f := fun _ : ℂ => (1 : ℝ))
    (g := fun z y => F (z,y)) hs hk
    (fun z y hzz hy => hz z hzz y hy)
    (locallyIntegrable_const (μ := (volume : Measure ℂ)) (1 : ℝ)) hf
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_one] using hh

lemma fderiv_integral_apply (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) (e : ℂ) :
    fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e =
      ∫ y : ℂ, paramDeriv F e (z,y) := by
  rw [(hasFDerivAt_integral hs hk hz hf hzz).fderiv]
  change (∫ y : ℂ, fderiv ℝ F (z,y)) (e,0) = _
  exact ContinuousLinearMap.integral_apply
    ((fderiv_section_continuous hs hf hzz).integrable_of_hasCompactSupport
      (fderiv_section_compact hs hk hz hzz)) _

lemma fderiv_section_apply (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) (y e : ℂ) :
    fderiv ℝ (fun z : ℂ => F (z,y)) z e = paramDeriv F e (z,y) := by
  have hd := ((hf (z,y) ⟨hz, mem_univ y⟩).contDiffAt
    ((hs.prod isOpen_univ).mem_nhds ⟨hz, mem_univ y⟩)).differentiableAt (by simp)
  have hpair : HasFDerivAt (fun x : ℂ => (x,y)) (ContinuousLinearMap.inl ℝ ℂ ℂ) z := by
    exact (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hc := hd.hasFDerivAt.comp z hpair
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L e) hc.fderiv

lemma second_integral_apply (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) (e : ℂ) :
    fderiv ℝ (fun z : ℂ => fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e) z e =
      ∫ y : ℂ, paramDeriv (paramDeriv F e) e (z,y) := by
  have he : (fun z : ℂ => fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e) =ᶠ[𝓝 z]
      (fun z : ℂ => ∫ y : ℂ, paramDeriv F e (z,y)) := by
    filter_upwards [hs.mem_nhds hzz] with x hx
    exact fderiv_integral_apply hs hk hz hf hx e
  rw [he.fderiv_eq]
  exact fderiv_integral_apply hs hk (partial_zero_outside hs hk.isClosed hz e)
    (partial_contDiffOn hs hf e) hzz e

lemma second_section_apply (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) (y e : ℂ) :
    fderiv ℝ (fun z : ℂ => fderiv ℝ (fun z : ℂ => F (z,y)) z e) z e =
      paramDeriv (paramDeriv F e) e (z,y) := by
  have he : (fun z : ℂ => fderiv ℝ (fun z : ℂ => F (z,y)) z e) =ᶠ[𝓝 z]
      (fun z : ℂ => paramDeriv F e (z,y)) := by
    filter_upwards [hs.mem_nhds hz] with x hx
    exact fderiv_section_apply hs hf hx y e
  rw [he.fderiv_eq]
  exact fderiv_section_apply hs (partial_contDiffOn hs hf e) hz y e

lemma integrable_section (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    Integrable (fun y : ℂ => F (z,y)) := by
  have hc : HasCompactSupport (fun y : ℂ => F (z,y)) :=
    HasCompactSupport.intro hk (hz z hzz)
  exact (hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    (fun y => ⟨hzz, mem_univ y⟩)).integrable_of_hasCompactSupport hc

lemma laplacian_directions_at {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    Δ f z =
      fderiv ℝ (fun x : ℂ => fderiv ℝ f x 1) z 1 +
      fderiv ℝ (fun x : ℂ => fderiv ℝ f x Complex.I) z Complex.I := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const _),
    fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const _)]
  simp

lemma laplacian_integral (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    Δ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z =
      ∫ y : ℂ, Δ (fun z : ℂ => F (z,y)) z := by
  have hfi : ContDiffAt ℝ ∞ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z :=
    ((integral_contDiffOn hs hk hz hf) z hzz).contDiffAt (hs.mem_nhds hzz)
  have hfs (y : ℂ) : ContDiffAt ℝ ∞ (fun z : ℂ => F (z,y)) z :=
    ((hf (z,y) ⟨hzz, mem_univ y⟩).contDiffAt
      ((hs.prod isOpen_univ).mem_nhds ⟨hzz, mem_univ y⟩)).comp z
      (contDiffAt_id.prodMk contDiffAt_const)
  have hi (e : ℂ) : Integrable (fun y : ℂ => paramDeriv (paramDeriv F e) e (z,y)) :=
    integrable_section hk
      (partial_zero_outside hs hk.isClosed (partial_zero_outside hs hk.isClosed hz e) e)
      (partial_contDiffOn hs (partial_contDiffOn hs hf e) e) hzz
  rw [laplacian_directions_at hfi, second_integral_apply hs hk hz hf hzz,
    second_integral_apply hs hk hz hf hzz, ← integral_add (hi 1) (hi Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [laplacian_directions_at (hfs y), second_section_apply hs hf hzz,
    second_section_apply hs hf hzz]

end StrictHotSpots.CompactParameter


namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental StrictHotSpots.DiskFormula

lemma correction_potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    Δ (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) z = 0 := by
  change Δ (fun z : ℂ => ∫ y : ℂ, correctionIntegrand f (z,y)) z = 0
  rw [CompactParameter.laplacian_integral hs hc.isCompact
    (F := correctionIntegrand f)
    (fun z _ y hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
    (correctionIntegrand_contDiffOn hf hn) hz]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : f y = 0
  · simp [correctionIntegrand, hy]
  · have hyt : y ∈ tsupport f := subset_tsupport _ hy
    have ha : AnalyticAt ℂ (fun z : ℂ => 1-z*star y) z :=
      analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
    have hh := (ha.harmonicAt_log_norm (hn z hz y hyt)).const_smul (c := f y)
    exact hh.2.self_of_nhds

lemma log_potential_eq (f : ℂ → ℝ) (z : ℂ) :
    ((fun x : ℂ => Real.log ‖x‖) ⋆ f) z = ∫ y : ℂ, f y * Real.log ‖z-y‖ := by
  rw [← convolution_flip]
  simp only [convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring


lemma potential_contDiffOn {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (potential f) s :=
  ((correction_potential_smooth hf hc hs hn).div_const _).sub
    ((log_potential_smooth hf hc).contDiffOn.div_const _)

lemma potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    Δ (potential f) z = -f z := by
  have ha := ((correction_potential_smooth hf hc hs hn) z hz).contDiffAt (hs.mem_nhds hz)
  have hb := (log_potential_smooth hf hc).contDiffAt (x := z)
  have he : potential f = (2 * Real.pi)⁻¹ •
      (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) -
      (2 * Real.pi)⁻¹ • ((fun x : ℂ => Real.log ‖x‖) ⋆ f) := by
    funext x
    simp only [potential, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have ha2 : ContDiffAt ℝ 2 ((2 * Real.pi)⁻¹ •
      (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖)) z :=
    (ha.const_smul ((2 * Real.pi)⁻¹)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hb2 : ContDiffAt ℝ 2 ((2 * Real.pi)⁻¹ •
      ((fun x : ℂ => Real.log ‖x‖) ⋆ f)) z :=
    (hb.const_smul ((2 * Real.pi)⁻¹)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [he, ha2.laplacian_sub hb2,
    laplacian_smul _ (ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplacian_smul _ (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    correction_potential_laplacian hf hc hs hn hz, log_potential_laplacian hf hc]
  simp only [smul_eq_mul, mul_zero, zero_sub, neg_inj]
  field_simp

lemma potential_eq_zero_on_circle (f : ℂ → ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    potential f z = 0 := by
  have he (y : ℂ) : ‖1-z*star y‖ = ‖z-y‖ := by
    have hh := disk_cross_identity z y
    rw [hz] at hh
    nlinarith [norm_nonneg (1-z*star y), norm_nonneg (z-y)]
  simp only [potential, he, log_potential_eq, sub_self]

lemma potential_eq_integral {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (_hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    potential f z = ∫ y : ℂ, green z y * f y := by
  have hi : Integrable (fun y : ℂ => f y * Real.log ‖1-z*star y‖) :=
    CompactParameter.integrable_section hc.isCompact
      (F := correctionIntegrand f)
      (fun z _ y hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
      (correctionIntegrand_contDiffOn hf hn) hz
  have hj : Integrable (fun y : ℂ => f y * Real.log ‖z-y‖) := by
    simpa only [norm_sub_rev z, mul_comm] using log_sub_mul_integrable hf.continuous hc z
  rw [potential, log_potential_eq, ← integral_div, ← integral_div,
    ← integral_sub (hi.div_const _) (hj.div_const _)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne z] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  · rw [green_eq_log (Ne.symm hy) (hn z hz y (subset_tsupport _ hfy))]
    ring

lemma exists_regular_neighborhood {f : ℂ → ℝ} (hc : HasCompactSupport f)
    (hd : tsupport f ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ z ∈ Metric.ball (0 : ℂ) R,
      ∀ y ∈ tsupport f, 1-z*star y ≠ 0 := by
  obtain ⟨a, ha, hsub⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    hc.isCompact.isClosed hd
  refine ⟨a⁻¹, (one_lt_inv₀ ha.1).mpr ha.2, ?_⟩
  intro z hz y hy
  have hz' : ‖z‖ < a⁻¹ := by simpa using hz
  have hy' : ‖y‖ < a := by simpa using hsub hy
  have hp : ‖z*star y‖ < 1 := by
    rw [norm_mul, norm_star]
    calc
      _ ≤ ‖z‖ * a := mul_le_mul_of_nonneg_left hy'.le (norm_nonneg _)
      _ < a⁻¹ * a := mul_lt_mul_of_pos_right hz' ha.1
      _ = 1 := inv_mul_cancel₀ ha.1.ne'
  intro he
  have hm : z*star y = 1 := (sub_eq_zero.mp he).symm
  rw [hm, norm_one] at hp
  exact lt_irrefl _ hp

lemma potential_smooth_near_closed_disk {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hd : tsupport f ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) R, Δ (potential f) z = -f z) := by
  obtain ⟨R,hR,hn⟩ := exists_regular_neighborhood hc hd
  exact ⟨R,hR,potential_contDiffOn hf hc Metric.isOpen_ball hn,
    fun z hz => potential_laplacian hf hc Metric.isOpen_ball hn hz⟩

end StrictHotSpots.GreenPotential




open InnerProductSpace
open scoped Laplacian ContDiff
namespace StrictHotSpots

lemma laplacian_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (g : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (x : E) :
    Δ (f ∘ g) x = Δ f (g x) := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map g)]
  have he : iteratedFDeriv ℝ 2 (f ∘ g) x =
      (iteratedFDeriv ℝ 2 f (g x)).compContinuousLinearMap (fun _ => g.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa [iteratedFDerivWithin_univ] using g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
      uniqueDiffOn_univ (Set.mem_univ (g x)) 2
  simp only [he, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> simp

end StrictHotSpots


namespace StrictHotSpots.PlaneGreen
open GreenPotential DiskH10

lemma source_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (source f) :=
  hf.comp complexIso.toContinuousLinearEquiv.contDiff

lemma source_compact {f : Plane → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (source f) :=
  hc.comp_homeomorph complexIso.toHomeomorph

lemma source_support {f : Plane → ℝ} (hs : tsupport f ⊆ disk) :
    tsupport (source f) ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  have he := Set.ext_iff.mp (tsupport_comp_eq_preimage f complexIso.toHomeomorph) z
  have hm : complexIso z ∈ disk := hs (he.mp hz)
  simpa [disk] using hm

lemma smooth_near_closed_disk {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) :
    ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball (0 : Plane) R, Δ (potential f) x = -f x) := by
  obtain ⟨R,hR,hu,hp⟩ := GreenPotential.potential_smooth_near_closed_disk
    (source_contDiff hf) (source_compact hc) (source_support hs)
  refine ⟨R,hR,?_,?_⟩
  · exact hu.comp complexIso.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => by simpa using hx)
  · intro x hx
    change Δ (GreenPotential.potential (source f) ∘ complexIso.symm) x = -f x
    rw [laplacian_comp_linearIsometryEquiv]
    have hh := hp (complexIso.symm x) (by simpa using hx)
    simpa [source] using hh

lemma zero_on_circle (f : Plane → ℝ) {x : Plane} (hx : ‖x‖ = 1) :
    potential f x = 0 :=
  GreenPotential.potential_eq_zero_on_circle (source f) (by simpa using hx)

lemma value_mk (w : H1 disk) (hw : w ∈ h10Submodule diskOpen) :
    H10.value diskOpen ⟨w,hw⟩ = H1.value w := rfl

lemma energy_mk (w : H1 disk) (hw : w ∈ h10Submodule diskOpen) (v : H10 diskOpen) :
    H10.energy diskOpen ⟨w,hw⟩ v = inner ℝ (H1.grad w) (H10.grad diskOpen v) := rfl

lemma exists_smooth_weak_solution {u f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hu : ContDiffOn ℝ ∞ u (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → u x = 0)
    (hf : MemLp f 2 (volume.restrict disk))
    (hp : ∀ x ∈ disk, Δ u x = -f x) :
    ∃ w : H10 (Ω := disk) diskOpen,
      (H10.value diskOpen w =ᵐ[volume.restrict disk] u) ∧
      ∀ v : H10 (Ω := disk) diskOpen,
        H10.energy diskOpen w v = inner ℝ (hf.toLp f) (H10.value diskOpen v) := by
  let h : HasH1Gradient disk u (gradient u) := smooth_memH1 hR hu
  have hm : h.toH1 ∈ h10Submodule diskOpen := smooth_zero_boundary_memH10 hR hu hz
  refine ⟨⟨h.toH1,hm⟩,?_,?_⟩
  · rw [value_mk, H1.value_toH1]
    exact h.1.coeFn_toLp
  · intro v
    rw [energy_mk]
    exact smooth_weak_poisson diskOpen (hu.mono (Metric.ball_subset_ball hR.le)) h hf hp v



lemma exists_dirichlet_representative {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) :
    ∃ u : H10 (Ω := disk) diskOpen,
      (H10.value diskOpen u =ᵐ[volume.restrict disk] potential f) ∧
      ∀ v : H10 (Ω := disk) diskOpen,
        H10.energy diskOpen u v =
          inner ℝ ((test_memLp (Ω := disk) hf hc).toLp f) (H10.value diskOpen v) := by
  have hex : ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball (0 : Plane) R, Δ (potential f) x = -f x) :=
    smooth_near_closed_disk (f := f) hf hc hs
  rcases hex with ⟨R,hR,hu,hp⟩
  refine exists_smooth_weak_solution (u := potential f) (f := f) (R := R) hR hu
    ?_ (test_memLp (Ω := disk) hf hc) ?_
  · intro x hx
    exact zero_on_circle f hx
  · intro x hx
    exact hp x (Metric.ball_subset_ball hR.le hx)

end StrictHotSpots.PlaneGreen







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.MeasurableL2Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (K : X × Y → ℝ) (hK : AEStronglyMeasurable K (μ.prod ν))
  (hrow : ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 ν)
  {B : ℝ} (hB : 0 ≤ B)
  (hbound : ∀ᵐ x ∂μ, (eLpNorm (fun y => K (x,y)) 2 ν).toReal ≤ B)

lemma operator_apply_ae (f : Lp ℝ 2 ν) :
    operator K hK hrow hB hbound f =ᵐ[μ] fun x => ∫ y, K (x,y) * f y ∂ν :=
  (apply_memLp K hK hrow hbound f).coeFn_toLp

end StrictHotSpots.MeasurableL2Kernel



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology
namespace StrictHotSpots

lemma eq_zero_of_inner_smoothTest_eq_zero {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ φ : smoothTestSpace Ω, inner ℝ (H1.value (smoothTestToH1 hΩ φ)) u = 0) :
    u = 0 := by
  have hl := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
    (fun φ hp hc hs => show (∫ x in Ω, φ x • u x) = 0 from by
      have ht := h ⟨φ,hp,hc,hs⟩
      have hv : H1.value (smoothTestToH1 hΩ ⟨φ,hp,hc,hs⟩) =
          (test_memLp (Ω := Ω) hp hc).toLp φ := rfl
      rw [hv, L2.inner_def] at ht
      convert ht using 1
      apply integral_congr_ae
      filter_upwards [(test_memLp (Ω := Ω) hp hc).coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      ring)
  apply Lp.ext
  filter_upwards [hh, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x hx hΩx hz
  rw [hz]
  exact hx hΩx

lemma smoothTest_dense_L2 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (fun φ : smoothTestSpace Ω => H1.value (smoothTestToH1 hΩ φ)) := by
  let T : smoothTestSpace Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    H1.value.toLinearMap.comp (smoothTestToH1 hΩ)
  have hz : T.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    change u = 0
    apply eq_zero_of_inner_smoothTest_eq_zero hΩ u
    intro φ
    exact (Submodule.mem_orthogonal _ _).mp hu (T φ) ⟨φ,rfl⟩
  have ht : T.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hz, Submodule.bot_orthogonal_eq_top]
  have hd : closure (Set.range T) = Set.univ := by
    change closure (T.range : Set (Lp ℝ 2 (volume.restrict Ω))) = Set.univ
    rw [← Submodule.topologicalClosure_coe, ht, Submodule.top_coe]
  exact dense_iff_closure_eq.mpr hd

end StrictHotSpots







open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


lemma solution_spec (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) (v : V) : B (solution B hB J f) v = ⟪f, J v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp only [solution, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]


lemma green_symmetric (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (f g : H) :
    ⟪green B hB J f, g⟫_ℝ = ⟪f, green B hB J g⟫_ℝ := by
  calc
    _ = ⟪g, J (solution B hB J f)⟫_ℝ := real_inner_comm _ _
    _ = B (solution B hB J g) (solution B hB J f) := (solution_spec B hB J g _).symm
    _ = B (solution B hB J f) (solution B hB J g) := hsym _ _
    _ = _ := solution_spec B hB J f _

end StrictHotSpots.DirichletOperator


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma integralOperator_ae (f : Lp ℝ 2 (volume.restrict disk)) :
    integralOperator f =ᵐ[volume.restrict disk] fun x => ∫ y in disk, kernel x y * f y :=
  MeasurableL2Kernel.operator_apply_ae _ _ _ _ _ f

lemma potential_eq_integral {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) {x : Plane} (hx : x ∈ disk) :
    potential f x = ∫ y in disk, kernel x y * f y := by
  obtain ⟨R,hR,hn⟩ := GreenPotential.exists_regular_neighborhood (source_compact hc)
    (source_support hs)
  have hx' : complexIso.symm x ∈ Metric.ball (0 : ℂ) R := by
    have : ‖x‖ < 1 := by simpa [disk] using hx
    simpa using this.trans hR
  have hh := GreenPotential.potential_eq_integral (source_contDiff hf) (source_compact hc)
    Metric.isOpen_ball hn hx'
  change GreenPotential.potential (source f) (complexIso.symm x) = _
  rw [hh]
  have he := complexIso.symm.measurePreserving.integral_comp
    complexIso.symm.toMeasurableEquiv.measurableEmbedding
    (fun z => DiskFormula.green (complexIso.symm x) z * source f z)
  simp only [source, complexIso.apply_symm_apply] at he
  simp only [source]
  rw [← he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
  simp [hfy, kernel]

lemma variationalOperator_test (f : smoothTestSpace disk) :
    variationalOperator (H1.value (smoothTestToH1 diskOpen f)) =ᵐ[volume.restrict disk]
      potential f := by
  obtain ⟨u,hu,he⟩ := exists_dirichlet_representative f.property.1 f.property.2.1 f.property.2.2
  let w := DirichletOperator.solution (H10.energy diskOpen)
    (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen)
    (H1.value (smoothTestToH1 diskOpen f))
  have hw : ∀ v, H10.energy diskOpen w v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) :=
    DirichletOperator.solution_spec _ _ _ _
  have he' : ∀ v, H10.energy diskOpen u v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) := he
  obtain ⟨_,_,hun⟩ := H10.existsUnique_energy_solution diskOpen diskBounded
    ((innerSL ℝ (H1.value (smoothTestToH1 diskOpen f))).comp (H10.value diskOpen))
  have heq : w = u := (hun w hw).trans (hun u he').symm
  change H10.value diskOpen w =ᵐ[volume.restrict disk] potential f
  rw [heq]
  exact hu



lemma integralOperator_eq_variationalOperator : integralOperator = variationalOperator := by
  apply DFunLike.coe_injective
  apply (smoothTest_dense_L2 diskOpen).equalizer integralOperator.continuous
    variationalOperator.continuous
  funext f
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [integralOperator_ae (H1.value (smoothTestToH1 diskOpen f)),
    variationalOperator_test f, ae_restrict_mem diskOpen.measurableSet] with x hx hu hxd
  rw [hx,hu,potential_eq_integral f.property.1 f.property.2.1 f.property.2.2 hxd]
  apply integral_congr_ae
  have hf : H1.value (smoothTestToH1 diskOpen f) =ᵐ[volume.restrict disk] f :=
    (test_memLp (Ω := disk) f.property.1 f.property.2.1).coeFn_toLp
  filter_upwards [hf] with y hy
  rw [hy]

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict Ω)


lemma energy_symmetric (u v : H10 hΩ) : energy hΩ u v = energy hΩ v u := by
  calc
    energy hΩ u v = inner ℝ (grad hΩ u) (grad hΩ v) := energy_apply hΩ u v
    _ = inner ℝ (grad hΩ v) (grad hΩ u) := real_inner_comm _ _
    _ = energy hΩ v u := (energy_apply hΩ v u).symm

lemma greenOperator_symmetric (f g : Lp ℝ 2 ν) :
    inner ℝ (greenOperator hΩ hb hC hν f) g =
      inner ℝ f (greenOperator hΩ hb hC hν g) :=
  DirichletOperator.green_symmetric (energy hΩ) (energy_coercive hΩ hb)
    (energy_symmetric hΩ) (weightedValue hΩ hC hν) f g

end StrictHotSpots.H10


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.DirichletOperator

lemma green_comp {V H K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) (S : H →L[ℝ] K) :
    green B hB (S.comp J) = (S.comp (green B hB J)).comp S.adjoint := by
  simp only [green, solution, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end StrictHotSpots.DirichletOperator
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma inclusion_ae (f : Lp ℝ 2 (volume.restrict disk)) : inclusion hC hν f =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν f

lemma inclusion_row (x : Plane) (hx : x ∈ disk) :
    inclusion hC hν ((kernel_memLp x hx).toLp (kernel x)) =
      (kernel_memLp_weighted hC hν x hx).toLp (kernel x) := by
  apply Lp.ext
  exact (inclusion_ae hC hν _).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq (kernel_memLp x hx).coeFn_toLp).trans
      (kernel_memLp_weighted hC hν x hx).coeFn_toLp.symm)

lemma integral_adjoint_row (f : Lp ℝ 2 ν) (x : Plane) (hx : x ∈ disk) :
    (∫ y in disk, kernel x y * (inclusion hC hν).adjoint f y) =
      ∫ y, kernel x y * f y ∂ν := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp x hx)
    (Lp.memLp ((inclusion hC hν).adjoint f)), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, inclusion_row hC hν x hx]
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp_weighted hC hν x hx)
    (Lp.memLp f), Lp.toLp_coeFn]



lemma weightedIntegralOperator_ae (f : Lp ℝ 2 ν) :
    weightedIntegralOperator hC hν f =ᵐ[ν] fun x => ∫ y, kernel x y * f y ∂ν := by
  have ha := (Measure.absolutelyContinuous_of_le_smul hν)
  filter_upwards [inclusion_ae hC hν (integralOperator ((inclusion hC hν).adjoint f)),
    ha.ae_eq (integralOperator_ae ((inclusion hC hν).adjoint f)),
    (ae_restrict_mem diskOpen.measurableSet).filter_mono ha.ae_le] with x hx hi hxd
  change inclusion hC hν (integralOperator ((inclusion hC hν).adjoint f)) x = _
  rw [hx,hi,integral_adjoint_row hC hν f x hxd]

lemma weightedIntegralOperator_eq_greenOperator : weightedIntegralOperator hC hν =
    H10.greenOperator diskOpen diskBounded hC hν := by
  unfold weightedIntegralOperator H10.greenOperator H10.weightedValue

  rw [DirichletOperator.green_comp, integralOperator_eq_variationalOperator]
  rfl



lemma weightedIntegralOperator_symmetric (f g : Lp ℝ 2 ν) :
    inner ℝ (weightedIntegralOperator hC hν f) g =
      inner ℝ f (weightedIntegralOperator hC hν g) := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_symmetric diskOpen diskBounded hC hν f g

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section KernelPositivityLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.BanachResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma symmetric (T : H →L[ℝ] H) (hT : ‖T‖ < 1)
    (hsym : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g)) (f g : H) :
    inner ℝ (resolvent T f) g = inner ℝ f (resolvent T g) := by
  have hf : resolvent T f - T (resolvent T f) = f :=
    congrArg (fun A : H →L[ℝ] H => A f) (resolvent_left T hT)
  have hg : resolvent T g - T (resolvent T g) = g :=
    congrArg (fun A : H →L[ℝ] H => A g) (resolvent_left T hT)
  calc
    inner ℝ (resolvent T f) g =
      inner ℝ (resolvent T f) (resolvent T g - T (resolvent T g)) := by rw [hg]
    _ = inner ℝ (resolvent T f - T (resolvent T f)) (resolvent T g) := by
      rw [inner_sub_left, inner_sub_right, hsym]
    _ = inner ℝ f (resolvent T g) := by rw [hf]
end StrictHotSpots.BanachResolvent

end
end KernelPositivityLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_KernelLimit
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section L2CutoffLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (s : Set X) (hs : MeasurableSet s)

lemma extension_ae (f : Lp ℝ 2 (ν.restrict s)) :
    extension s hs f =ᵐ[ν] s.indicator f := (extension_memLp s hs f).coeFn_toLp

lemma extension_norm (f : Lp ℝ 2 (ν.restrict s)) : ‖extension s hs f‖ = ‖f‖ := by
  change ‖(extension_memLp s hs f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  rfl

lemma extension_norm_le : ‖extension (ν := ν) s hs‖ ≤ 1 := by
  apply (extension (ν := ν) s hs).opNorm_le_bound (by norm_num)
  intro f
  simp [extension_norm]

lemma restriction_ae (f : Lp ℝ 2 ν) : restriction s f =ᵐ[ν.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

lemma restriction_norm (f : Lp ℝ 2 ν) : ‖restriction s f‖ ≤ ‖f‖ := by
  change (eLpNorm (restriction s f) 2 (ν.restrict s)).toReal ≤ (eLpNorm f 2 ν).toReal
  rw [eLpNorm_congr_ae (restriction_ae s f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

lemma restriction_norm_le : ‖restriction (ν := ν) s‖ ≤ 1 := by
  apply (restriction (ν := ν) s).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using restriction_norm s f

lemma restriction_extension (f : Lp ℝ 2 (ν.restrict s)) :
    restriction s (extension s hs f) = f := by
  apply Lp.ext
  filter_upwards [restriction_ae s (extension s hs f), (extension_ae s hs f).restrict,
    ae_restrict_mem hs] with x hx he hxs
  rw [hx,he,indicator_of_mem hxs]

lemma extension_inner (f : Lp ℝ 2 (ν.restrict s)) (g : Lp ℝ 2 ν) :
    inner ℝ (extension s hs f) g = inner ℝ f (restriction s g) := by
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
  have he : (fun x => g x * extension s hs f x) =ᵐ[ν]
      s.indicator (fun x => g x * f x) := by
    filter_upwards [extension_ae s hs f] with x hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  rw [integral_congr_ae he, integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [restriction_ae s g] with x hx
  rw [hx]

lemma extension_eq_adjoint : extension (ν := ν) s hs = (restriction s).adjoint := by
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).2 (extension_inner s hs)

lemma extension_inner_extension (f g : Lp ℝ 2 (ν.restrict s)) :
    inner ℝ (extension s hs f) (extension s hs g) = inner ℝ f g := by
  rw [extension_inner, restriction_extension]

lemma projection_ae (f : Lp ℝ 2 ν) : projection s hs f =ᵐ[ν] s.indicator f := by
  filter_upwards [extension_ae s hs (restriction s f),
    ae_imp_of_ae_restrict (restriction_ae s f)] with x hx hr
  change extension s hs (restriction s f) x = _
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [hxs, hr hxs]
  · simp [hxs]

lemma projection_norm (f : Lp ℝ 2 ν) : ‖projection s hs f‖ ≤ ‖f‖ := by
  exact (extension_norm s hs _).le.trans (restriction_norm s f)

lemma projection_norm_le : ‖projection (ν := ν) s hs‖ ≤ 1 := by
  apply (projection (ν := ν) s hs).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using projection_norm s hs f

end StrictHotSpots.L2Cutoff

end L2CutoffLayer

section CutoffConvergenceLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma projection_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hex : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ s n) (f : Lp ℝ 2 ν) :
    Tendsto (fun n => projection (s n) (hs n) f) atTop (𝓝 f) := by
  let hf : ∀ n, MemLp ((s n).indicator f) 2 ν :=
    fun n => (Lp.memLp f).indicator (hs n)
  have ht := L2Limits.tendsto_toLp_of_dominated hf (Lp.memLp f) (Lp.memLp f).norm
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ s n <;> simp [hx])
    (by
      filter_upwards [hex] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  have he (n : ℕ) : projection (s n) (hs n) f = (hf n).toLp _ :=
    Lp.ext ((projection_ae (s n) (hs n) f).trans (hf n).coeFn_toLp.symm)
  simpa only [← he, Lp.toLp_coeFn] using ht

end StrictHotSpots.L2Cutoff
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_strong_tendsto_moving (Q : ℕ → E →L[ℝ] E) (A : E →L[ℝ] E)
    {d : ℝ} (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => Q n (v n)) atTop (𝓝 (A w)) := by
  have hz : Tendsto (fun n => Q n (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => d * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul d
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  simpa only [map_sub, sub_add_cancel, zero_add] using hz.add (hs w)

lemma compression_norm_le (T P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    ‖P.comp (T.comp P)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖P‖ * (‖T‖ * ‖P‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hP
      (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = ‖T‖ := by ring

lemma compression_strong_tendsto (T : E →L[ℝ] E) (P : ℕ → E →L[ℝ] E)
    (hP : ∀ᶠ n in atTop, ‖P n‖ ≤ 1)
    (hs : ∀ v, Tendsto (fun n => P n v) atTop (𝓝 v)) (f : E) :
    Tendsto (fun n => (P n).comp (T.comp (P n)) f) atTop (𝓝 (T f)) := by
  exact bounded_strong_tendsto_moving P (ContinuousLinearMap.id ℝ E) hP hs
    (T.continuous.continuousAt.tendsto.comp (hs f))

end StrictHotSpots.BanachResolvent
end
end CutoffConvergenceLayer

section CutoffOperatorsLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (s : Set X) (hs : MeasurableSet s)

lemma restrictedOperator_norm_le (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    ‖restrictedOperator s hs T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖restriction (ν := ν) s‖ * (‖T‖ * ‖extension (ν := ν) s hs‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul (restriction_norm_le s)
      (mul_le_mul_of_nonneg_left (extension_norm_le s hs) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = ‖T‖ := by ring

lemma compressedOperator_norm_le (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    ‖compressedOperator s hs T‖ ≤ ‖T‖ :=
  BanachResolvent.compression_norm_le T (projection s hs) (projection_norm_le s hs)

lemma extension_intertwine (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : Lp ℝ 2 (ν.restrict s)) :
    extension s hs (restrictedOperator s hs T f) =
      compressedOperator s hs T (extension s hs f) := by
  change extension s hs (restriction s (T (extension s hs f))) =
    extension s hs (restriction s (T (extension s hs (restriction s (extension s hs f)))))
  rw [restriction_extension]

lemma resolvent_extension (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hT : ‖T‖ < 1)
    (f : Lp ℝ 2 (ν.restrict s)) :
    BanachResolvent.resolvent (compressedOperator s hs T) (extension s hs f) =
      extension s hs (BanachResolvent.resolvent (restrictedOperator s hs T) f) := by
  symm
  apply BanachResolvent.resolvent_solution _ ((compressedOperator_norm_le s hs T).trans_lt hT)
  rw [← extension_intertwine, ← map_sub]
  congr 1
  exact congrArg (fun A : Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 (ν.restrict s) => A f)
    (BanachResolvent.resolvent_left _ ((restrictedOperator_norm_le s hs T).trans_lt hT))

lemma resolvent_inner_extension (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hT : ‖T‖ < 1)
    (f g : Lp ℝ 2 (ν.restrict s)) :
    inner ℝ (extension s hs f)
      (BanachResolvent.resolvent (compressedOperator s hs T) (extension s hs g)) =
      inner ℝ f (BanachResolvent.resolvent (restrictedOperator s hs T) g) := by
  rw [resolvent_extension s hs T hT, extension_inner_extension]

end StrictHotSpots.L2Cutoff
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk) (s : Set Plane)

lemma inclusion_restrict : inclusion hC (restrictDensity hν s) =
    (L2Cutoff.restriction s).comp (inclusion hC hν) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [inclusion_ae hC (restrictDensity hν s) f,
    L2Cutoff.restriction_ae s (inclusion hC hν f), (inclusion_ae hC hν f).restrict]
    with x hx hr hi
  rw [hx, show ((L2Cutoff.restriction s).comp (inclusion hC hν)) f x = f x from hr.trans hi]

lemma weightedIntegralOperator_restrict (hs : MeasurableSet s) :
    weightedIntegralOperator hC (restrictDensity hν s) =
      L2Cutoff.restrictedOperator s hs (weightedIntegralOperator hC hν) := by
  unfold weightedIntegralOperator L2Cutoff.restrictedOperator
  rw [inclusion_restrict hC hν s, ContinuousLinearMap.adjoint_comp, L2Cutoff.extension_eq_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

end StrictHotSpots.PlaneGreen
end
end CutoffOperatorsLayer

section DiskCutoffLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma cutoffRadius_tendsto : Tendsto cutoffRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1)
  simpa only [sub_zero] using
    ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma eventually_mem_cutoffSet (x : Plane) (hx : x ∈ disk) :
    ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  have ht := cutoffRadius_tendsto.eventually (eventually_gt_nhds (show ‖x‖ < 1 by simpa [disk] using hx))
  filter_upwards [ht] with n hn
  simpa [cutoffSet] using hn.le

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma ae_eventually_mem_cutoffSet : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  filter_upwards [ae_mem_disk hν] with x hx
  exact eventually_mem_cutoffSet x hx

include hν in
lemma cutoffProjection_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) f)
      atTop (𝓝 f) :=
  L2Cutoff.projection_tendsto cutoffSet cutoffSet_measurable (ae_eventually_mem_cutoffSet hν) f

include hν in
lemma cutoff_integral_tendsto {f : Plane → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x in cutoffSet n, f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hm : ∀ n, AEStronglyMeasurable ((cutoffSet n).indicator f) ν :=
    fun n => hf.aestronglyMeasurable.indicator (cutoffSet_measurable n)
  have ht := tendsto_integral_filter_of_dominated_convergence (f := f) (fun x => ‖f x‖)
    (Eventually.of_forall hm)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ cutoffSet n <;> simp [hx]) hf.norm
    (by
      filter_upwards [ae_eventually_mem_cutoffSet hν] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  simpa only [integral_indicator (cutoffSet_measurable _)] using ht

include hC hν in
lemma smoothedPoisson_cutoff_tendsto (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    Tendsto (fun n => smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x)
      atTop (𝓝 (smoothedPoisson (ν := ν) s x)) :=
  cutoff_integral_tendsto hν (product_green_poisson_integrable hC hν x hx s)

lemma smoothedPoisson_cutoff_L2_tendsto [IsFiniteMeasure ν] (s : Boundary) :
    Tendsto (fun n => (smoothedPoisson_full_memLp hC hν s (cutoffSet n)).toLp
      (smoothedPoisson (ν := ν.restrict (cutoffSet n)) s)) atTop
      (𝓝 ((smoothedPoisson_memLp hC hν s).toLp (smoothedPoisson (ν := ν) s))) := by
  apply L2Limits.tendsto_toLp_of_dominated
    (fun n => smoothedPoisson_full_memLp hC hν s (cutoffSet n))
    (smoothedPoisson_memLp hC hν s) (smoothedPoisson_memLp hC hν s)
  · apply Eventually.of_forall
    intro n
    filter_upwards [ae_mem_disk hν] with x hx
    rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν (cutoffSet n)) s hx)]
    exact smoothedPoisson_restrict_le hC hν s (cutoffSet n) hx
  · filter_upwards [ae_mem_disk hν] with x hx
    exact smoothedPoisson_cutoff_tendsto hC hν s hx

end StrictHotSpots.PlaneGreen
end
end DiskCutoffLayer

section FullBoundaryKernelLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.BanachResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma apply_eq_add (T : H →L[ℝ] H) (hT : ‖T‖ < 1) (f : H) :
    resolvent T f = f + resolvent T (T f) := by
  have he := congrArg (fun A : H →L[ℝ] H => A f) (resolvent_right T hT)
  have hh : resolvent T f - resolvent T (T f) = f := by
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, map_sub] using he
  exact sub_eq_iff_eq_add.mp hh

lemma apply_eq_add_left (T : H →L[ℝ] H) (hT : ‖T‖ < 1) (f : H) :
    resolvent T f = f + T (resolvent T f) := by
  have he := congrArg (fun A : H →L[ℝ] H => A f) (resolvent_left T hT)
  have hh : resolvent T f - T (resolvent T f) = f := by
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self] using he
  exact sub_eq_iff_eq_add.mp hh

lemma inner_two_terms (T : H →L[ℝ] H) (hT : ‖T‖ < 1)
    (hsym : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g)) (f g : H) :
    inner ℝ f (resolvent T g) = inner ℝ f g + inner ℝ f (T g) +
      inner ℝ (T f) (resolvent T (T g)) := by
  have h1 := congrArg (fun v => inner ℝ f v) (apply_eq_add T hT g)
  have h2 := congrArg (fun v => inner ℝ f v) (apply_eq_add_left T hT (T g))
  rw [inner_add_right] at h1 h2
  rw [← hsym f (resolvent T (T g))] at h2
  rw [h1, h2]
  ring

end StrictHotSpots.BanachResolvent
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma compactSmoothedRow_eq (n : ℕ) (s : Boundary) :
    weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s) =
    L2Cutoff.restriction (cutoffSet n) (cutoffSmoothedRow hC hν n s) := by
  apply Lp.ext
  filter_upwards [weightedIntegralOperator_ae hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s),
    L2Cutoff.restriction_ae (cutoffSet n) (cutoffSmoothedRow hC hν n s),
    ((smoothedPoisson_full_memLp hC hν s (cutoffSet n)).coeFn_toLp).restrict] with x hx hr hs
  rw [hx,hr,show cutoffSmoothedRow hC hν n s x =
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x from hs]
  apply integral_congr_ae
  filter_upwards [(poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp]
    with y hy
  rw [show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s y = poisson s y from hy]

lemma extendedSmoothedRow_tendsto (s : Boundary) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s)) atTop (𝓝 (smoothedRow hC hν s)) := by
  apply BanachResolvent.bounded_strong_tendsto_moving
    (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n))
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 ν))
    (Eventually.of_forall fun n => L2Cutoff.projection_norm_le _ _)
    (cutoffProjection_tendsto hν)
  exact smoothedPoisson_cutoff_L2_tendsto hC hν s



end StrictHotSpots.PlaneGreen
end
end FullBoundaryKernelLayer

section PoissonProductsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_measurable (s : Boundary) : Measurable (poisson s) := by
  unfold poisson DiskFormula.poisson
  fun_prop

lemma poisson_invnorm_bound (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    poisson s x ≤ Real.pi⁻¹ * ‖(s : Plane)-x‖⁻¹ := by
  have hh := DiskFormula.poisson_invnorm_bound (complexIso.symm s) (complexIso.symm x)
    (by simpa using s.property) (by simpa [disk] using hx)
  simpa only [poisson, ← map_sub, LinearIsometryEquiv.norm_map] using hh

lemma poisson_product_bound (s t : Boundary) (hst : s ≠ t) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ x ∈ disk, poisson s x * poisson t x ≤ A * (poisson s x + poisson t x) := by
  let D : ℝ := ‖(s : Plane)-(t : Plane)‖ / 2
  have hD : 0 < D := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
    (fun h => hst (Subtype.ext h)))) (by norm_num)
  let A : ℝ := Real.pi⁻¹ * D⁻¹
  refine ⟨A, mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (inv_nonneg.mpr hD.le), fun x hx => ?_⟩
  have hdist : 2*D ≤ ‖(s : Plane)-x‖ + ‖(t : Plane)-x‖ := by
    have hh := norm_add_le ((s : Plane)-x) (x-(t : Plane))
    have he : (s : Plane)-x+(x-(t : Plane)) = (s : Plane)-(t : Plane) := by abel
    rw [he, norm_sub_rev x (t : Plane)] at hh
    dsimp [D]
    linarith
  have hb (v : Boundary) (hv : D ≤ ‖(v : Plane)-x‖) : poisson v x ≤ A := by
    apply (poisson_invnorm_bound v hx).trans
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using one_div_le_one_div_of_le hD hv) (inv_nonneg.mpr Real.pi_pos.le)
  have hs := poisson_nonneg s ⟨x,hx⟩
  have ht := poisson_nonneg t ⟨x,hx⟩
  by_cases hd : D ≤ ‖(s : Plane)-x‖
  · have h1 := mul_le_mul_of_nonneg_right (hb s hd) ht
    have h2 : A * poisson t x ≤ A * (poisson s x + poisson t x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by dsimp [A]; positivity)
    exact h1.trans h2
  · have h1 := mul_le_mul_of_nonneg_left (hb t (by linarith)) hs
    have h2 : poisson s x * A ≤ A * (poisson s x + poisson t x) := by
      have hA : 0 ≤ A := by dsimp [A]; positivity
      nlinarith
    exact h1.trans h2

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma poisson_integrable (s : Boundary) : Integrable (poisson s) ν :=
  (poisson_memLp_three_halves_weighted hC hν s).integrable (by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num)

include hC hν in
lemma poisson_product_integrable (s t : Boundary) (hst : s ≠ t) :
    Integrable (fun x => poisson s x * poisson t x) ν := by
  obtain ⟨A,_,hA⟩ := poisson_product_bound s t hst
  apply (((poisson_integrable hC hν s).add (poisson_integrable hC hν t)).const_mul A).mono'
    ((poisson_measurable s).mul (poisson_measurable t)).aestronglyMeasurable
  filter_upwards [ae_mem_disk hν] with x hx
  change ‖poisson s x * poisson t x‖ ≤ A * (poisson s x + poisson t x)
  rw [Real.norm_of_nonneg (mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩))]
  exact hA x hx

include hC hν in
lemma poisson_smoothed_cutoff_tendsto (s t : Boundary) :
    Tendsto (fun n => ∫ x in cutoffSet n, poisson s x *
      smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν) atTop
      (𝓝 (∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν)) := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  let f (n : ℕ) (x : Plane) := (cutoffSet n).indicator (fun x => poisson s x *
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x) x
  have hm n : AEStronglyMeasurable (f n) ν :=
    (((poisson_measurable s).mul (smoothedPoisson_measurable t)).indicator
      (cutoffSet_measurable n)).aestronglyMeasurable
  have hd n : ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖poisson s x‖ * B := by
    filter_upwards [ae_mem_disk hν] with x hx
    by_cases he : x ∈ cutoffSet n
    · dsimp only [f]
      rw [indicator_of_mem he, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν (cutoffSet n)) t hx)]
      exact (smoothedPoisson_restrict_le hC hν t (cutoffSet n) hx).trans
        (le_abs_self _ |>.trans (hB x hx t))
    · simp only [f, indicator_of_notMem he, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _ |>.trans (hB x hx t))
  have hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop
      (𝓝 (poisson s x * smoothedPoisson (ν := ν) t x)) := by
    filter_upwards [ae_mem_disk hν, ae_eventually_mem_cutoffSet hν] with x hx he
    apply ((smoothedPoisson_cutoff_tendsto hC hν t hx).const_mul (poisson s x)).congr'
    filter_upwards [he] with n hn
    simp [f,hn]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun x => ‖poisson s x‖ * B)
    (Eventually.of_forall hm) (Eventually.of_forall hd)
    ((poisson_integrable hC hν s).norm.mul_const B) hl
  simpa only [f, integral_indicator (cutoffSet_measurable _)] using hh

end StrictHotSpots.PlaneGreen
end
end PoissonProductsLayer

section CutoffBoundaryLimitsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma cutoff_poisson_inner (n : ℕ) (s t : Boundary) :
    inner ℝ (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t) =
      ∫ x in cutoffSet n, poisson s x * poisson t x ∂ν :=
  (MeasurableL2Kernel.integral_mul_eq_inner
    (poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
    (poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t)).symm

lemma cutoff_poisson_smoothed_inner (n : ℕ) (s t : Boundary) :
    inner ℝ (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
      (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
        (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t)) =
      ∫ x in cutoffSet n, poisson s x *
        smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν := by
  rw [compactSmoothedRow_eq hC hν, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp,
    L2Cutoff.restriction_ae (cutoffSet n) (cutoffSmoothedRow hC hν n t),
    ((smoothedPoisson_full_memLp hC hν t (cutoffSet n)).coeFn_toLp).restrict] with x hs hr ht
  change L2Cutoff.restriction (cutoffSet n) (cutoffSmoothedRow hC hν n t) x *
    poissonRow _ _ s x = _
  rw [hr,show cutoffSmoothedRow hC hν n t x =
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x from ht,
    show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s x = poisson s x from hs,
    mul_comm]

lemma cutoffN_expansion (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (n : ℕ) (s t : Boundary) :
    cutoffN hC hν n s t = boundaryInteraction s t +
      (∫ x in cutoffSet n, poisson s x * poisson t x ∂ν) +
      (∫ x in cutoffSet n, poisson s x * smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν) +
      inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))
        (BanachResolvent.resolvent (cutoffOperator hC hν n)
          (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n t))) := by
  have hn : ‖weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))‖ < 1 := by
    rw [weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)]
    exact (L2Cutoff.restrictedOperator_norm_le _ _ _).trans_lt hT
  have he := L2Cutoff.resolvent_inner_extension (cutoffSet n) (cutoffSet_measurable n)
    (weightedIntegralOperator hC hν) hT
    (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s))
    (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t))
  rw [← weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)] at he
  simp only [compactSmoothedRow_eq hC hν] at he
  change inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))
    (BanachResolvent.resolvent (cutoffOperator hC hν n)
      (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n t))) = _ at he
  unfold cutoffN boundaryN
  rw [BanachResolvent.inner_two_terms _ hn (weightedIntegralOperator_symmetric hC _),
    cutoff_poisson_inner, cutoff_poisson_smoothed_inner hC hν]
  simp only [compactSmoothedRow_eq hC hν]
  rw [← he]
  ring

omit [IsFiniteMeasure ν] in
lemma cutoffOperator_strong_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => cutoffOperator hC hν n f) atTop (𝓝 (weightedIntegralOperator hC hν f)) :=
  BanachResolvent.compression_strong_tendsto _ _
    (Eventually.of_forall fun n => L2Cutoff.projection_norm_le (cutoffSet n) (cutoffSet_measurable n)) (cutoffProjection_tendsto hν) f

lemma cutoff_resolvent_smoothed_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s : Boundary) :
    Tendsto (fun n => BanachResolvent.resolvent (cutoffOperator hC hν n)
      (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s)))
      atTop (𝓝 (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (smoothedRow hC hν s))) := by
  apply BanachResolvent.resolvent_strong_tendsto_moving _ _ hT hT
    (Eventually.of_forall fun n => L2Cutoff.compressedOperator_norm_le _ _ _)
    (cutoffOperator_strong_tendsto hC hν)
  exact extendedSmoothedRow_tendsto hC hν s

lemma cutoffN_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) (hst : s ≠ t) :
    Tendsto (fun n => cutoffN hC hν n s t) atTop (𝓝 (fullBoundaryN hC hν s t)) := by
  have ht := (((tendsto_const_nhds (x := boundaryInteraction s t)).add
    (cutoff_integral_tendsto hν (poisson_product_integrable hC hν s t hst))).add
    (poisson_smoothed_cutoff_tendsto hC hν s t)).add
    ((extendedSmoothedRow_tendsto hC hν s).inner (cutoff_resolvent_smoothed_tendsto hC hν hT t))
  simpa only [cutoffN_expansion hC hν hT, fullBoundaryN] using ht

end StrictHotSpots.PlaneGreen
end
end CutoffBoundaryLimitsLayer



end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryRRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryN_eq (s t : Boundary) : fullBoundaryN hC hν s t =
    boundaryInteraction s t + fullBoundaryR hC hν s t := by
  unfold fullBoundaryN fullBoundaryR firstInteraction secondInteraction tailInteraction
  ring

end StrictHotSpots.PlaneGreen
end BoundaryRRepresentationScalarSupportLayer

section BoundaryRPropertiesScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryInteraction_symm (s t : Boundary) : boundaryInteraction s t = boundaryInteraction t s := by
  simp only [boundaryInteraction,DiskFormula.boundaryInteraction,norm_sub_rev (complexIso.symm (t : Plane))]

lemma fullBoundaryN_symm (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    fullBoundaryN hC hν s t = fullBoundaryN hC hν t s := by
  by_cases hst : s = t
  · subst t; rfl
  have he (n : ℕ) : cutoffN hC hν n s t = cutoffN hC hν n t s := by
    have hn : ‖weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))‖ < 1 := by
      rw [weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)]
      exact (L2Cutoff.restrictedOperator_norm_le _ _ _).trans_lt hT
    unfold cutoffN boundaryN
    rw [boundaryInteraction_symm s t]
    congr 1
    rw [← BanachResolvent.symmetric _ hn (weightedIntegralOperator_symmetric hC _)]
    exact real_inner_comm _ _
  exact tendsto_nhds_unique (cutoffN_tendsto hC hν hT s t hst)
    (by simpa only [he] using cutoffN_tendsto hC hν hT t s (Ne.symm hst))

lemma fullBoundaryR_symm_oai (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    fullBoundaryR hC hν s t = fullBoundaryR hC hν t s := by
  have hn := fullBoundaryN_symm hC hν hT s t
  rw [fullBoundaryN_eq,fullBoundaryN_eq,boundaryInteraction_symm s t] at hn
  exact add_left_cancel hn

end StrictHotSpots.PlaneGreen
end BoundaryRPropertiesScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm_oai := @OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm_oai
