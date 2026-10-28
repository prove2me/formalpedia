-- Prove2me | solution 1 for OAI.StrictHotSpots.PlaneGreen.value_K_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:44:45.830344+00:00
-- url     : https://prove2.me/submissions/b46f783a-f808-4a80-8a8d-e203e70dd5e7

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_boundarySolution_weak

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

lemma resolvent_right (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    resolvent A * (1 - A) = 1 := geom_series_mul_neg A hA

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal




open MeasureTheory Filter
open scoped Topology ENNReal

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



lemma green_norm_le (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ v : V, ‖J v‖ ^ 2 ≤ d * B v v) : ‖green B hB J‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  let u := solution B hB J f
  have h0 := hsub u
  have hs : B u u = ⟪f, J u⟫_ℝ := solution_spec B hB J f u
  rw [hs] at h0
  have hi : ⟪f, J u⟫_ℝ ≤ ‖f‖ * ‖J u‖ := real_inner_le_norm _ _
  have ht : ‖J u‖ ^ 2 ≤ d * (‖f‖ * ‖J u‖) :=
    h0.trans (mul_le_mul_of_nonneg_left hi hd)
  change ‖J u‖ ≤ d * ‖f‖
  by_cases hz : ‖J u‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖J u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

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


lemma greenOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 hΩ, ‖weightedValue hΩ hC hν u‖ ^ 2 ≤
      d * ‖grad hΩ u‖ ^ 2) : ‖greenOperator hΩ hb hC hν‖ ≤ d := by
  apply DirichletOperator.green_norm_le (energy hΩ) (energy_coercive hΩ hb)
    (weightedValue hΩ hC hν) hd
  intro u
  simpa only [energy_apply, real_inner_self_eq_norm_sq] using hsub u

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



lemma weightedIntegralOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) : ‖weightedIntegralOperator hC hν‖ ≤ d := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_norm_le diskOpen diskBounded hC hν hd hsub

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Poisson
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section HarmonicLiftCombinedLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)

include hb in
lemma h10_eq_zero_of_grad_norm_sq (v : H10 ho) (hv : ‖H10.grad ho v‖^2 = 0) : v = 0 := by
  obtain ⟨K,hK,h⟩ := H10.energy_coercive ho hb
  have he : H10.energy ho v v = 0 := (real_inner_self_eq_norm_sq _).trans hv
  have hm : K * ‖v‖^2 ≤ 0 := by
    calc
      _ = K * ‖v‖ * ‖v‖ := by ring
      _ ≤ H10.energy ho v v := h v
      _ = 0 := he
  have : ‖v‖^2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _)))

end StrictHotSpots.SubcriticalExtension
end HarmonicLiftCombinedLayer

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

lemma restriction_ae (f : Lp ℝ 2 ν) : restriction s f =ᵐ[ν.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

lemma restriction_norm (f : Lp ℝ 2 ν) : ‖restriction s f‖ ≤ ‖f‖ := by
  change (eLpNorm (restriction s f) 2 (ν.restrict s)).toReal ≤ (eLpNorm f 2 ν).toReal
  rw [eLpNorm_congr_ae (restriction_ae s f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

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

end StrictHotSpots.BanachResolvent
end
end CutoffConvergenceLayer

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

section SubcriticalUniquenessScalarSupportLayer

open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)

lemma weakPotential_sub {F G : H1 Ω}
    (hF : WeakPotential ho hC hν F) (hG : WeakPotential ho hC hν G) :
    WeakPotential ho hC hν (F-G) := by
  intro v
  have hg := H1.grad.map_sub F G
  have hh := (observe hC hν).map_sub F G
  calc
    _ = inner ℝ (H1.grad F-H1.grad G) (H10.grad ho v) :=
      congrArg (fun z : Lp Plane 2 (volume.restrict Ω) => inner ℝ z (H10.grad ho v)) hg
    _ = inner ℝ (H1.grad F) (H10.grad ho v)-inner ℝ (H1.grad G) (H10.grad ho v) :=
      inner_sub_left _ _ _
    _ = inner ℝ (observe hC hν F) (H10.weightedValue ho hC hν v) -
        inner ℝ (observe hC hν G) (H10.weightedValue ho hC hν v) :=
      congrArg₂ (fun a b : ℝ => a-b) (hF v) (hG v)
    _ = inner ℝ (observe hC hν F-observe hC hν G) (H10.weightedValue ho hC hν v) :=
      (inner_sub_left _ _ _).symm
    _ = _ := congrArg (fun z : Lp ℝ 2 ν => inner ℝ z (H10.weightedValue ho hC hν v)) hh.symm

include hb in
lemma weakPotential_zero_class {d : ℝ} (hd : d < 1)
    (hsub : ∀ v : H10 ho, ‖H10.weightedValue ho hC hν v‖^2 ≤ d*‖H10.grad ho v‖^2)
    {F : H1 Ω} (hF : WeakPotential ho hC hν F) (h0 : ∃ v : H10 ho, F = v.val) : F = 0 := by
  obtain ⟨v,rfl⟩ := h0
  have he := hF v
  change inner ℝ (H10.grad ho v) (H10.grad ho v) =
    inner ℝ (H10.weightedValue ho hC hν v) (H10.weightedValue ho hC hν v) at he
  simp only [real_inner_self_eq_norm_sq] at he
  have hz : ‖H10.grad ho v‖^2 = 0 := by nlinarith [hsub v,sq_nonneg ‖H10.grad ho v‖]
  exact congrArg (fun v : H10 ho => v.val) (h10_eq_zero_of_grad_norm_sq ho hb v hz)

include hb in
lemma weakPotential_unique {d : ℝ} (hd : d < 1)
    (hsub : ∀ v : H10 ho, ‖H10.weightedValue ho hC hν v‖^2 ≤ d*‖H10.grad ho v‖^2)
    {A F G : H1 Ω} (hF : WeakPotential ho hC hν F) (hG : WeakPotential ho hC hν G)
    (hFA : ∃ v : H10 ho, F-A = v.val) (hGA : ∃ v : H10 ho, G-A = v.val) : F = G := by
  apply sub_eq_zero.mp
  apply weakPotential_zero_class ho hb hC hν hd hsub
    (weakPotential_sub ho hC hν hF hG)
  obtain ⟨v,hv⟩ := hFA
  obtain ⟨w,hw⟩ := hGA
  refine ⟨v-w,?_⟩
  change F-G=v.val-w.val
  calc
    _ = (F-A)-(G-A) := by abel
    _ = _ := congrArg₂ (fun x y : H1 Ω => x-y) hv hw

end StrictHotSpots.SubcriticalExtension
end SubcriticalUniquenessScalarSupportLayer

section BoundaryMeasurabilityScalarSupportLayer

section BoundaryMeasurabilityLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)

lemma poissonRow_continuous : Continuous (poissonRow hR hR1) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply L2Limits.tendsto_toLp_of_dominated
    (hb := memLp_const (1 / (2 * Real.pi * (1-R)^2)))
  · apply Eventually.of_forall
    intro t
    filter_upwards [hR] with x hx
    change ‖DiskFormula.poisson (complexIso.symm (t : Plane)) (complexIso.symm x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (DiskFormula.poisson_nonneg _ _ (by simpa using hx.trans_lt hR1))]
    exact DiskFormula.poisson_bounded _ _ (by simpa using t.property) (by simpa using hx) hR1
  · filter_upwards [hR] with x hx
    exact (poisson_continuous_boundary ⟨x, by simpa [disk] using hx.trans_lt hR1⟩).continuousAt

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma smoothedRow_stronglyMeasurable : StronglyMeasurable (smoothedRow hC hν) := by
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun n s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s))
  · intro n
    have he : (fun s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
        (cutoffSmoothedRow hC hν n s)) =
        fun s => L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)
          (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
            (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)) := by
      funext s
      rw [compactSmoothedRow_eq]
      rfl
    rw [he]
    apply Continuous.stronglyMeasurable
    exact (L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)).continuous.comp
      ((weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))).continuous.comp
        (poissonRow_continuous (cutoff_ae_norm n) (cutoffRadius_lt_one n)))
  · exact tendsto_pi_nhds.mpr (extendedSmoothedRow_tendsto hC hν)

lemma smoothedPoisson_joint_measurable :
    Measurable (fun z : Boundary × Plane => smoothedPoisson (ν := ν) z.1 z.2) := by
  have h1 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have h2 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hk := measurable_kernel.comp h1
  have hp := poisson_joint_measurable.comp h2
  dsimp only [Function.comp_def] at hk hp
  have hm := hk.mul hp
  change Measurable (fun z : Boundary × Plane =>
    ∫ y, kernel z.2 y * poisson z.1 y ∂ν)
  have hh : StronglyMeasurable (fun z : Boundary × Plane =>
      ∫ y, kernel z.2 y * poisson z.1 y ∂ν) :=
    hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  exact hh.measurable

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BochnerL2RowsScalarSupportLayer

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Rows

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]


lemma integral_eq_toLp {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (havg : MemLp (fun x => ∫ a, r a x ∂μ) 2 ν)
    (hpair : ∀ g : Lp ℝ 2 ν, Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν)) :
    (∫ a, R a ∂μ) = havg.toLp (fun x => ∫ a, r a x ∂μ) := by
  apply ext_inner_left ℝ
  intro g
  rw [← integral_inner hR g, L2.inner_def]
  calc
    (∫ a, inner ℝ g (R a) ∂μ) = ∫ a, ∫ x, g x * r a x ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hr a] with x hx
      simp only [hx, Real.inner_apply]
    _ = ∫ x, ∫ a, g x * r a x ∂μ ∂ν := integral_integral_swap (hpair g)
    _ = ∫ x, inner ℝ (g x) ((havg.toLp (fun x => ∫ a, r a x ∂μ)) x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [havg.coeFn_toLp] with x hx
      rw [hx, integral_const_mul]
      exact (Real.inner_apply _ _).symm

lemma integrable_pair_of_bound {r : A → B → ℝ}
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) (g : Lp ℝ 2 ν) :
    Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν) := by
  have hg : Integrable (fun z : A × B => ‖g z.2‖ * M) (μ.prod ν) :=
    ((Lp.memLp g).integrable (by norm_num)).norm.comp_snd μ |>.mul_const M
  apply hg.mono' ((Lp.memLp g).aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)
  filter_upwards [hM] with z hz
  change ‖g z.2 * r z.1 z.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

lemma integral_eq_toLp_of_bound {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) :
    (∫ a, R a ∂μ) = (average_memLp hm hM).toLp (fun x => ∫ a, r a x ∂μ) :=
  integral_eq_toLp hR hr (average_memLp hm hM) (integrable_pair_of_bound hm hM)

end StrictHotSpots.L2Rows
end BochnerL2RowsScalarSupportLayer

section BoundaryExtensionScalarSupportLayer

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma smoothedRow_uniform_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖smoothedRow hC hν s‖ ≤ M := by
  obtain ⟨B,hB,h⟩ := green_poisson_uniform_bound hC hν
  refine ⟨(measureUnivNNReal ν : ℝ) ^ (2 : ℝ)⁻¹ * B, by positivity, fun s => ?_⟩
  apply Lp.norm_le_of_ae_bound hB
  filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
  rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
  exact h x hxd s

lemma smoothedRow_integrable {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun s => f s • smoothedRow hC hν s) boundaryMeasure := by
  obtain ⟨M,hM,h⟩ := smoothedRow_uniform_bound hC hν
  apply Integrable.of_bound (hf.aestronglyMeasurable.smul
    (smoothedRow_stronglyMeasurable hC hν).aestronglyMeasurable) (B*M)
  filter_upwards [] with s
  change ‖f s • smoothedRow hC hν s‖ ≤ B*M
  rw [norm_smul]
  exact mul_le_mul (hB s) (h s) (norm_nonneg _) (le_trans (norm_nonneg (f s)) (hB s))

include hC hν in
lemma green_poisson_boundary_integrable (p : disk) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2)
      (boundaryMeasure.prod ν) := by
  have hm : Measurable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2) :=
    (measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul poisson_joint_measurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).const_mul (kernel p x)
  · apply ((kernel_memLp_weighted hC hν p p.property).integrable (by norm_num)).norm.congr
    filter_upwards [ae_mem_disk hν] with x hx
    rw [show (∫ s, ‖kernel p x * poisson s x‖ ∂boundaryMeasure) = ‖kernel p x‖ by
      simp_rw [norm_mul, Real.norm_of_nonneg (poisson_nonneg _ ⟨x,hx⟩)]
      rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]]

include hC hν in
lemma green_poisson_data_integrable (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2 * f z.1)
      (boundaryMeasure.prod ν) := by
  apply ((green_poisson_boundary_integrable hC hν p).norm.mul_const B).mono'
    (((measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul
      poisson_joint_measurable).mul (hf.comp measurable_fst)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖kernel p z.2 * poisson z.1 z.2 * f z.1‖ ≤ ‖kernel p z.2 * poisson z.1 z.2‖ * B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg (kernel p z.2 * poisson z.1 z.2))

include hC hν in
lemma smoothedPoisson_average (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  calc
    _ = ∫ s, ∫ x, kernel p x * poisson s x * f s ∂ν ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [integral_mul_const]
      exact mul_comm _ _
    _ = ∫ x, ∫ s, kernel p x * poisson s x * f s ∂boundaryMeasure ∂ν :=
      integral_integral_swap (green_poisson_data_integrable hC hν p hf hB)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [poissonExtension,smul_eq_mul, mul_assoc, integral_const_mul]

lemma smoothedRow_average {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s • smoothedRow hC hν s ∂boundaryMeasure) =
      weightedIntegralOperator hC hν (poissonL2 hν hf hB) := by
  obtain ⟨M,_,hM⟩ := green_poisson_uniform_bound hC hν
  have hm : Measurable (fun z : Boundary × Plane => f z.1 * smoothedPoisson (ν := ν) z.1 z.2) :=
    (hf.comp measurable_fst).mul smoothedPoisson_joint_measurable
  have hb : ∀ᵐ z ∂boundaryMeasure.prod ν,
      ‖f z.1 * smoothedPoisson (ν := ν) z.1 z.2‖ ≤ B*M := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2
    filter_upwards [] with s
    filter_upwards [ae_mem_disk hν] with x hx
    change ‖f s * smoothedPoisson (ν := ν) s x‖ ≤ B*M
    rw [norm_mul]
    exact mul_le_mul (hB s) (hM x hx s) (norm_nonneg _)
      (le_trans (norm_nonneg (f s)) (hB s))
  have hr (s : Boundary) : (f s • smoothedRow hC hν s) =ᵐ[ν]
      (fun x => f s * smoothedPoisson (ν := ν) s x) := by
    filter_upwards [Lp.coeFn_smul (f s) (smoothedRow hC hν s),
      (smoothedPoisson_memLp hC hν s).coeFn_toLp] with x hx hpx
    rw [hx]
    change f s * smoothedRow hC hν s x = _
    rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hpx]
  rw [L2Rows.integral_eq_toLp_of_bound (r := fun s x => f s * smoothedPoisson (ν := ν) s x)
    (smoothedRow_integrable hC hν hf hB) hr hm hb]
  · apply Lp.ext
    filter_upwards [(L2Rows.average_memLp (r := fun s x => f s * smoothedPoisson (ν := ν) s x) hm hb).coeFn_toLp,
      weightedIntegralOperator_ae hC hν (poissonL2 hν hf hB),ae_mem_disk hν] with x hx ht hxd
    rw [hx,ht,smoothedPoisson_average hC hν ⟨x,hxd⟩ hf hB]
    apply integral_congr_ae
    filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with y hy
    rw [show poissonL2 hν hf hB y = poissonExtension f y from hy]
end StrictHotSpots.PlaneGreen
end BoundaryExtensionScalarSupportLayer

section BoundaryKRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

omit [IsFiniteMeasure ν] in
lemma inner_row (p : disk) (g : Lp ℝ 2 ν) :
    inner ℝ (row hC hν p) g = ∫ x, kernel p x * g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(column_memLp hC hν p).coeFn_toLp] with x hx
  change inner ℝ (row hC hν p x) (g x) = _
  rw [show row hC hν p x = kernel x p from hx,kernel_symm x p,Real.inner_apply]

lemma inner_row_poissonL2 (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    inner ℝ (row hC hν p) (poissonL2 hν hf hB) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  rw [inner_row]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with x hx
  rw [show poissonL2 hν hf hB x = poissonExtension f x from hx]


lemma fullBoundaryK_representation (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, fullBoundaryK hC hν p s * f s ∂boundaryMeasure) =
      fullExtension hC hν hf hB p := by
  let T := weightedIntegralOperator hC hν
  let R := BanachResolvent.resolvent T
  have hI := smoothedRow_integrable hC hν hf hB
  have hRI := R.integrable_comp hI
  have htail : (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) =
      inner ℝ (row hC hν p) (R (T (poissonL2 hν hf hB))) := by
    calc
      _ = ∫ s, inner ℝ (row hC hν p) (R (f s • smoothedRow hC hν s)) ∂boundaryMeasure := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [map_smul,inner_smul_right]
      _ = _ := by rw [integral_inner hRI, R.integral_comp_comm hI,smoothedRow_average hC hν hf hB]
  have htailI : Integrable (fun s => f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s))) boundaryMeasure := by
    convert hRI.const_inner (row hC hν p) using 1
    funext s
    rw [map_smul,inner_smul_right]
  have hP : Integrable (fun s => poisson s p * f s) boundaryMeasure := by
    apply ((poisson_boundary_integrable p).norm.mul_const B).mono'
      ((poisson_continuous_boundary p).measurable.mul hf).aestronglyMeasurable
    filter_upwards [] with s
    change ‖poisson s p * f s‖ ≤ ‖poisson s p‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB s) (norm_nonneg _)
  have hF : Integrable (fun s => f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := by
    have h := (green_poisson_data_integrable hC hν p hf hB).integral_prod_left
    convert h using 1
    funext s
    change f s * smoothedPoisson (ν := ν) s p = ∫ x, kernel p x * poisson s x * f s ∂ν
    rw [integral_mul_const]
    exact mul_comm _ _
  calc
    _ = (∫ s, poisson s p * f s ∂boundaryMeasure) +
        (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) +
        (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) := by
      have hPF : Integrable (fun s => poisson s p * f s + f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := hP.add hF
      rw [← integral_add hP hF,← integral_add hPF htailI]
      apply integral_congr_ae
      filter_upwards [] with s
      unfold fullBoundaryK
      dsimp only [R,T]
      ring
    _ = fullExtension hC hν hf hB p := by
      rw [smoothedPoisson_average hC hν p hf hB, htail, ← inner_row_poissonL2 hC hν p hf hB]
      change poissonExtension f p + inner ℝ (row hC hν p) _ + inner ℝ (row hC hν p) _ = _
      have hr := BanachResolvent.apply_eq_add (weightedIntegralOperator hC hν) hT (poissonL2 hν hf hB)
      rw [fullExtension,hr,inner_add_right]
      ring
end StrictHotSpots.PlaneGreen
end BoundaryKRepresentationScalarSupportLayer

section BoundaryFormScalarSupportLayer



open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma boundary_continuous_bound {f : Boundary → E} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖f s‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max M 0,le_max_right _ _,fun s => (hM s (mem_univ s)).trans (le_max_left _ _)⟩

end StrictHotSpots.PlaneGreen
end BoundaryFormScalarSupportLayer
end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniformL3

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StrictHotSpots.L2Limits



lemma unifIntegrable_iff'_compat {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} {p : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) : UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine ⟨(min δ 1).toNNReal, ?_, fun i s hmeas hμ => ?_⟩
  · exact ENNReal.toNNReal_pos (lt_min hδ one_pos).ne' (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    apply hs i s hmeas
    refine hμ.trans ?_
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne]
    exact min_le_left _ _

lemma unifIntegrable_two_of_three {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hb : ∀ i, eLpNorm (f i) 3 μ ≤ B) :
    UnifIntegrable f 2 μ := by
  apply unifIntegrable_iff'_compat
  intro ε hε
  have ht : Tendsto (fun t : ℝ => B * (ENNReal.ofReal t) ^ (1/6 : ℝ)) (𝓝 0) (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hB (by norm_num : (0:ℝ)<1/6)).comp
      (by simpa using ENNReal.continuous_ofReal.tendsto (0:ℝ))
  have he : ∀ᶠ t : ℝ in 𝓝 0, B * (ENNReal.ofReal t) ^ (1/6:ℝ) < ε :=
    ht.eventually (eventually_lt_nhds hε)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ENNReal.ofReal (r/2), ENNReal.ofReal_pos.mpr (half_pos hr),
    fun i s hs hμs => ?_⟩
  have htt : B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) < ε :=
    hrb (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
      using (half_lt_self hr))
  calc
    eLpNorm (f i) 2 (μ.restrict s) ≤ eLpNorm (f i) 3 (μ.restrict s) * (μ s)^(1/6:ℝ) := by
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        ENNReal.toReal_ofNat, show (1/(2:ℝ)-1/3) = 1/6 by norm_num] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
          (by norm_num : (2:ℝ≥0∞)≤3) (hf i).restrict)
    _ ≤ B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) := by
      gcongr
      exact (eLpNorm_mono_measure (f i) Measure.restrict_le_self).trans (hb i)
    _ ≤ ε := htt.le

end StrictHotSpots.L2Limits
end
end UniformL3

section GreenRowContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma kernel_continuousAt_left {x y : Plane} (hx : x ∈ disk) (hy : y ∈ disk)
    (hxy : x ≠ y) : ContinuousAt (fun z => kernel z y) x := by
  have hx1 : ‖x‖ < 1 := by simpa [disk] using hx
  have hy1 : ‖y‖ < 1 := by simpa [disk] using hy
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hy2 : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : ‖x-y‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have ha : 1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 ≠ 0 := by positivity
  simp_rw [kernel_plane_formula]
  fun_prop (disch := assumption)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma row_eq_toLp (x : disk) : row hC hν x =
    (kernel_memLp_weighted hC hν x x.property).toLp (kernel x) := by
  apply Lp.ext
  filter_upwards [(column_memLp hC hν x).coeFn_toLp,
    (kernel_memLp_weighted hC hν x x.property).coeFn_toLp] with y hy hx
  exact hy.trans ((kernel_symm y x).trans hx.symm)



theorem row_continuous [IsFiniteMeasure ν] : Continuous (row hC hν) := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  simp only [Function.comp_def]
  simp_rw [row_eq_toLp hC hν]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => kernel (u n))
    (fun n => kernel_memLp_weighted hC hν _ (u n).property) (kernel x)
    (kernel_memLp_weighted hC hν _ x.property)).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (kernel_memLp_weighted hC hν _ (u n).property).aestronglyMeasurable)
    (kernel_memLp_weighted hC hν _ x.property)
  · obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
    exact L2Limits.unifIntegrable_two_of_three
      (fun n => (kernel_memLp_three_weighted hC hν _ (u n).property).aestronglyMeasurable)
      hB (fun n => h _ (u n).property)
  · have hne : ∀ᵐ y ∂ν, y ≠ (x:Plane) :=
      ((volume.restrict disk).ae_ne (x:Plane)).filter_mono
        (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    filter_upwards [ae_mem_disk hν,hne] with y hyd hyx
    exact (kernel_continuousAt_left x.property hyd hyx.symm).tendsto.comp
      ((continuous_subtype_val.tendsto x).comp hu)


lemma green_integral_eq_inner (f : Lp ℝ 2 ν) (x : disk) :
    (∫ y, kernel x y * f y ∂ν) = inner ℝ (row hC hν x) f := by
  rw [row_eq_toLp hC hν,MeasurableL2Kernel.integral_mul_eq_inner
    (kernel_memLp_weighted hC hν x x.property) (Lp.memLp f),Lp.toLp_coeFn]

include hC hν in
lemma green_integral_continuous [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    Continuous (fun x : disk => ∫ y, kernel x y * f y ∂ν) := by
  simp_rw [green_integral_eq_inner hC hν]
  exact (row_continuous hC hν).inner continuous_const

end StrictHotSpots.PlaneGreen
end
end GreenRowContinuous

section BoundaryPoissonTransport

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local notation "τ" => (2*Real.pi)

lemma poissonExtension_eq_planePoisson (f : C(Boundary,ℝ)) {x : Plane} (hx : x ∈ disk) :
    poissonExtension f x = Douglas.planePoisson (boundaryAngleData f) x := by
  rw [poissonExtension,integral_boundary_angles]
  unfold Douglas.planePoisson
  rw [Douglas.poissonExtension_re_eq_circleAverage _
    (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx)]
  unfold Real.circleAverage
  simp_rw [poisson_eq_standard]
  simp only [smul_eq_mul,Pi.mul_apply,mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Douglas.circleDatum_circleMap,boundaryAngleData_apply,Complex.ofReal_re]
  have ha : angleBoundary (θ : AddCircle τ) = circleBoundary (Circle.exp θ) := rfl
  rw [ha]
  change poissonKernel 0 (complexIso.symm x)
      (complexIso.symm (complexIso (Circle.exp θ : ℂ))) * _ =
    poissonKernel 0 (complexIso.symm x) (circleMap 0 1 θ) * _
  simp [circleMap,Circle.coe_exp]


lemma boundaryPoissonH1_value_ae (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    (H1.value (boundaryPoissonH1 f hf) : Plane → ℝ) =ᵐ[volume.restrict disk]
      poissonExtension f := by
  rw [boundaryPoissonH1,H1.value_toH1]
  filter_upwards [(Douglas.lipschitz_planePoisson_hasH1Gradient (boundaryAngleData f)
    A.coe_nonneg (boundaryAngleData_lipschitz f hf)).1.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x hx hxd
  exact hx.trans (poissonExtension_eq_planePoisson f hxd).symm

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryPoissonH1_observe (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf) =
      poissonL2 hν f.continuous.measurable hB := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value (boundaryPoissonH1 f hf)),
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (boundaryPoissonH1_value_ae f hf),
    (poissonExtension_memLp hν f.continuous.measurable hB).coeFn_toLp] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonTransport

section GreenSolveContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.DirichletOperator
variable {V H K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
lemma solution_comp (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (L : H →L[ℝ] K) :
    solution B hB (L.comp J) = (solution B hB J).comp L.adjoint := by
  unfold solution
  rw [ContinuousLinearMap.adjoint_comp]
  rfl
end StrictHotSpots.DirichletOperator
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma solve_value_eq_integralOperator (f : Lp ℝ 2 ν) :
    H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν f) =
      integralOperator ((inclusion hC hν).adjoint f) := by
  have he := DirichletOperator.solution_comp (H10.energy diskOpen)
    (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen) (inclusion hC hν)
  have hev := congrArg (fun L => H10.value diskOpen (L f)) he
  exact hev.trans (congrArg (fun L => L ((inclusion hC hν).adjoint f))
    integralOperator_eq_variationalOperator.symm)



lemma solve_value_ae (f : Lp ℝ 2 ν) :
    (H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν f) : Plane → ℝ)
      =ᵐ[volume.restrict disk] fun x => ∫ y, kernel x y*f y ∂ν := by
  rw [solve_value_eq_integralOperator hC hν]
  filter_upwards [integralOperator_ae ((inclusion hC hν).adjoint f),
    ae_restrict_mem diskOpen.measurableSet] with x hx hxd
  exact hx.trans (integral_adjoint_row hC hν f x hxd)



lemma boundarySolutionValue_eq_fullExtension [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x = fullExtension hC hν f.continuous.measurable hB x := by
  rw [boundarySolutionValue,fullExtension,green_integral_eq_inner hC hν]

lemma poissonExtension_continuousOn (f : C(Boundary,ℝ)) :
    ContinuousOn (poissonExtension f) disk := by
  apply (Douglas.planePoisson_contDiffOn (boundaryAngleData f)).continuousOn.congr
  intro x hx
  exact poissonExtension_eq_planePoisson f hx

lemma boundarySolutionValue_continuousOn [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    ContinuousOn (boundarySolutionValue hC hν f hB) disk := by
  apply (poissonExtension_continuousOn f).add
  exact continuousOn_iff_continuous_domRestrict.mpr (green_integral_continuous hC hν _)

lemma boundarySolution_value_eq [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    H1.value (boundarySolution hC hν f hf) = H1.value (boundaryPoissonH1 f hf) +
      H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν
        (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          (poissonL2 hν f.continuous.measurable hB))) := by
  have hr : BanachResolvent.resolvent (H10.greenOperator diskOpen diskBounded hC hν)
      (SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf)) =
      BanachResolvent.resolvent (weightedIntegralOperator hC hν)
        (poissonL2 hν f.continuous.measurable hB) := by
    rw [boundaryPoissonH1_observe hC hν f hf hB,
      ← weightedIntegralOperator_eq_greenOperator hC hν]
  have hv := H1.value.map_add (boundaryPoissonH1 f hf)
    (SubcriticalExtension.solve diskOpen diskBounded hC hν
      (BanachResolvent.resolvent (H10.greenOperator diskOpen diskBounded hC hν)
        (SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf)))).val
  exact hv.trans (congrArg (fun z => H1.value (boundaryPoissonH1 f hf) +
    H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν z)) hr)

lemma value_add_ae (a b : Lp ℝ 2 (volume.restrict disk))
    (f g : Plane → ℝ) (ha : a =ᵐ[volume.restrict disk] f)
    (hb : b =ᵐ[volume.restrict disk] g) :
    (a+b : Lp ℝ 2 (volume.restrict disk)) =ᵐ[volume.restrict disk] fun x => f x+g x := by
  filter_upwards [Lp.coeFn_add a b,ha,hb] with x h h1 h2
  exact h.trans (congrArg₂ (fun a b : ℝ => a+b) h1 h2)

lemma boundarySolution_value_ae [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (H1.value (boundarySolution hC hν f hf) : Plane → ℝ) =ᵐ[volume.restrict disk]
      boundarySolutionValue hC hν f hB := by
  rw [boundarySolution_value_eq hC hν f hf hB]
  exact value_add_ae _ _ _ _ (boundaryPoissonH1_value_ae f hf)
    (solve_value_ae hC hν _)



theorem boundarySolution_K [IsFiniteMeasure ν]
    (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x =
      ∫ s, fullBoundaryK hC hν x s * f s ∂boundaryMeasure := by
  rw [boundarySolutionValue_eq_fullExtension hC hν]
  exact (fullBoundaryK_representation hC hν hT x f.continuous.measurable hB).symm

end StrictHotSpots.PlaneGreen
end
end GreenSolveContinuous

section BoundarySolutionIdentification

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)




lemma boundarySolution_eq_of_trace {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) :
    boundarySolution hC hν f hf = hv.toH1 := by
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  exact SubcriticalExtension.weakPotential_unique diskOpen diskBounded hC hν hd1 hsub
    (boundarySolution_weak hC hν hn f hf) hp (boundarySolution_class hC hν f hf)
    (boundaryPoissonH1_real_class f hf hφ hc hv hb)

lemma boundarySolutionValue_eq_of_trace [IsFiniteMeasure ν]
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) :
    EqOn (boundarySolutionValue hC hν f hB) φ disk := by
  have he := boundarySolution_value_ae hC hν f hf hB
  rw [boundarySolution_eq_of_trace hC hν hd0 hd1 hsub f hf hφ hc hv hb hp,H1.value_toH1] at he
  exact Measure.eqOn_open_of_ae_eq (he.symm.trans hv.1.coeFn_toLp) diskOpen
    (boundarySolutionValue_continuousOn hC hν f hB) hφ.continuousOn



theorem value_K_of_trace_oai [IsFiniteMeasure ν]
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) (x : disk) :
    φ x = ∫ s, fullBoundaryK hC hν x s*f s ∂boundaryMeasure := by
  obtain ⟨B,_,hB⟩ := boundary_continuous_bound f.continuous
  have he := boundarySolutionValue_eq_of_trace hC hν hd0 hd1 hsub f hf hB hφ hc hv hb hp x.property
  exact he.symm.trans (boundarySolution_K hC hν
    ((weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1) f hB x)

end StrictHotSpots.PlaneGreen
end
end BoundarySolutionIdentification


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.PlaneGreen.value_K_of_trace_oai := @OAI.StrictHotSpots.PlaneGreen.value_K_of_trace_oai
