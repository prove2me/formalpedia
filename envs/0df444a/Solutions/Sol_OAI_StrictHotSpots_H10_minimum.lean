-- Prove2me | solution 1 for OAI.StrictHotSpots.H10.minimum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:22:34.133583+00:00
-- url     : https://prove2.me/submissions/5b0fc2d0-acda-4108-96f0-e7eb75b65e5d

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

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


lemma green_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) : green B hB J f = J (solution B hB J f) := rfl

lemma green_symmetric (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (f g : H) :
    ⟪green B hB J f, g⟫_ℝ = ⟪f, green B hB J g⟫_ℝ := by
  calc
    _ = ⟪g, J (solution B hB J f)⟫_ℝ := real_inner_comm _ _
    _ = B (solution B hB J g) (solution B hB J f) := (solution_spec B hB J g _).symm
    _ = B (solution B hB J f) (solution B hB J g) := hsym _ _
    _ = _ := solution_spec B hB J f _

lemma green_nonneg (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (f : H) : 0 ≤ ⟪f, green B hB J f⟫_ℝ := by
  rw [green_apply, ← solution_spec B hB J f (solution B hB J f)]
  obtain ⟨C, hC, h⟩ := hB
  exact (mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (norm_nonneg _)).trans (h _)



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


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section CompactRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma rowOperator_apply_ae (r : Lp H 2 μ) (v : H) :
    rowOperator r v =ᵐ[μ] fun x => inner ℝ v (r x) :=
  (innerSL ℝ v).coeFn_compLp r

lemma rowOperator_compact_simple (r : Lp.simpleFunc H 2 μ) :
    IsCompactOperator (rowOperator (r : Lp H 2 μ)) := by
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range (Lp.simpleFunc.toSimpleFunc r))
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Lp.simpleFunc.toSimpleFunc r).finite_range
  have he : rowOperator (r : Lp H 2 μ) =
      ((rowOperator (r : Lp H 2 μ)).comp V.subtypeL).comp V.orthogonalProjectionOnto := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [rowOperator_apply_ae (r : Lp H 2 μ) v,
      rowOperator_apply_ae (r : Lp H 2 μ) (V.orthogonalProjectionOnto v),
      Lp.simpleFunc.toSimpleFunc_eq_toFun r] with x hx hy hr
    change rowOperator (r : Lp H 2 μ) v x =
      rowOperator (r : Lp H 2 μ) (V.orthogonalProjectionOnto v) x
    rw [hx, hy, ← hr]
    have hmem : (Lp.simpleFunc.toSimpleFunc r) x ∈ V := Submodule.subset_span ⟨x, rfl⟩
    exact (V.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨_,hmem⟩ v).symm
  rw [he]
  exact (isCompactOperator_of_locallyCompactSpace_dom V.orthogonalProjectionOnto).clm_comp
    ((rowOperator (r : Lp H 2 μ)).comp V.subtypeL)



theorem rowOperator_compact (r : Lp H 2 μ) : IsCompactOperator (rowOperator r) := by
  have hc : IsClosed {f : Lp H 2 μ | IsCompactOperator (rowOperator f)} :=
    isClosed_setOfPred_isCompactOperator.preimage
      (rowOperator (μ := μ) (H := H)).continuous
  apply closure_minimal (fun f hf => rowOperator_compact_simple ⟨f,hf⟩) hc
  exact Lp.simpleFunc.dense (by norm_num) r

end StrictHotSpots.CompactRows
end CompactRowsCombinedLayer

section MeasurableRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows

lemma measurable_of_dist {α E : Type*} [MeasurableSpace α] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : α → E} (h : ∀ y, Measurable (fun x => dist (f x) y)) : Measurable f := by
  let B : Set (Set E) := {s | ∃ y r, s = Metric.ball y r}
  have hb : TopologicalSpace.IsTopologicalBasis B :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      (by rintro s ⟨y,r,rfl⟩; exact Metric.isOpen_ball)
      (by intro x s hx hs
          obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hs x hx
          exact ⟨Metric.ball x r, ⟨x,r,rfl⟩, Metric.mem_ball_self hr, hrs⟩)
  rw [BorelSpace.measurable_eq (α := E), hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨y,r,rfl⟩
  exact measurableSet_lt (h y) measurable_const

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] [IsSeparable ν]

local instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

attribute [local instance] OAI.StrictHotSpots.CompactRows.instMeasurableSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfNatENNReal_solutions
local instance instBorelSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfNatENNReal_solutions : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩

lemma measurable_toLp_rows (K : X × Y → ℝ) (hK : Measurable K)
    (hrow : ∀ x, MemLp (fun y => K (x,y)) 2 ν) :
    Measurable (fun x => (hrow x).toLp (fun y => K (x,y))) := by
  apply measurable_of_dist
  intro f
  let R := fun x => (hrow x).toLp (fun y => K (x,y))
  have he (x : X) : dist (R x) f = Real.sqrt (∫ y, (K (x,y) - f y)^2 ∂ν) := by
    rw [dist_eq_norm]
    have hs : ∫ y, (K (x,y) - f y)^2 ∂ν = ‖R x - f‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (R x) f, (hrow x).coeFn_toLp] with y hy hz
      simp only [Pi.sub_apply] at hy
      rw [real_inner_self_eq_norm_sq, hy, hz, Real.norm_eq_abs, sq_abs]
    rw [hs, Real.sqrt_sq (norm_nonneg _)]
  have hm : Measurable (fun p : X × Y => (K p - f p.2)^2) :=
    (hK.sub ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).pow_const 2
  simpa only [← he] using ((hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).sqrt

end StrictHotSpots.CompactRows
end MeasurableRowsCombinedLayer

section CompactCoerciveCombinedLayer
open Set
open scoped InnerProductSpace Topology
namespace StrictHotSpots.CompactCoercive
variable {E H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma finite_projection_approx (T : E →L[ℝ] H) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Submodule ℝ H, ∃ _ : FiniteDimensional ℝ U,
      ‖T - U.starProjection.comp T‖ ≤ ε := by
  obtain ⟨s,hs,hcover⟩ := Metric.totallyBounded_iff.mp
    (hT.isCompact_closure_image_closedBall 1).totallyBounded ε hε
  let U := Submodule.span ℝ s
  let : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ hs
  refine ⟨U,inferInstance,ContinuousLinearMap.opNorm_le_of_unit_norm hε.le ?_⟩
  intro x hx
  have hmem : T x ∈ closure (T '' Metric.closedBall 0 1) :=
    subset_closure ⟨x,by simpa using hx.le,rfl⟩
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hmem)
  change ‖T x - U.starProjection (T x)‖ ≤ ε
  have hmin := U.starProjection_minimal (T x)
  rw [hmin]
  exact (ciInf_le (by exact ⟨0, by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩)
    (⟨y,Submodule.subset_span hy⟩ : U)).trans (by exact (show ‖T x - y‖ < ε by simpa [Metric.mem_ball, dist_eq_norm] using hxy).le)



lemma observation_compact [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (S : H →L[ℝ] V)
    (hS : ∀ f v, B (S f) v = inner ℝ f (J v))
    (hc : IsCompactOperator (J.comp S)) : IsCompactOperator J := by
  obtain ⟨C,hC,hcoer⟩ := hB
  have hcl : J ∈ closure {A : V →L[ℝ] H | IsCompactOperator A} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    let q : ℝ := δ / (2 * (‖B‖ + 1))
    have hq : 0 < q := div_pos hδ (mul_pos (by norm_num) (by positivity))
    obtain ⟨U,hU,happrox⟩ := finite_projection_approx (J.comp S) hc
      (mul_pos hC (sq_pos_of_pos hq))
    let : FiniteDimensional ℝ U := hU
    let A : V →L[ℝ] H := U.starProjection.comp J
    have hAc : IsCompactOperator A :=
      ((isCompactOperator_of_locallyCompactSpace_rng U.subtypeL).comp_clm
        U.orthogonalProjectionOnto).comp_clm J
    refine ⟨A,hAc,?_⟩
    have ha : ‖J - A‖ ≤ ‖B‖ * q := by
      apply ContinuousLinearMap.opNorm_le_bound (J - A) (mul_nonneg (norm_nonneg B) hq.le)
      intro v
      let w := J v - U.starProjection (J v)
      have hwproj : inner ℝ w (U.starProjection (J v)) = 0 :=
        U.starProjection_inner_eq_zero (J v) _ (U.orthogonalProjectionOnto (J v)).property
      have hwJ : inner ℝ w (J v) = ‖w‖^2 := by
        calc
          _ = inner ℝ w (w + U.starProjection (J v)) := by
            congr 1; dsimp [w]; abel
          _ = _ := by rw [inner_add_right, hwproj, add_zero, real_inner_self_eq_norm_sq]
      have hwTproj : inner ℝ w (U.starProjection ((J.comp S) w)) = 0 :=
        U.starProjection_inner_eq_zero (J v) _ (U.orthogonalProjectionOnto ((J.comp S) w)).property
      have ht : inner ℝ w ((J.comp S) w) ≤ C * q^2 * ‖w‖^2 := by
        calc
          _ = inner ℝ w (((J.comp S) - U.starProjection.comp (J.comp S)) w) := by
            change inner ℝ w (J (S w)) = inner ℝ w (J (S w) - U.starProjection (J (S w)))
            have hz : inner ℝ w (U.starProjection (J (S w))) = 0 := hwTproj
            rw [inner_sub_right, hz, sub_zero]
          _ ≤ ‖w‖ * ‖((J.comp S) - U.starProjection.comp (J.comp S)) w‖ :=
            real_inner_le_norm _ _
          _ ≤ ‖w‖ * ((C * q^2) * ‖w‖) := by
            gcongr
            exact (((J.comp S) - U.starProjection.comp (J.comp S)).le_opNorm w).trans
              (mul_le_mul_of_nonneg_right happrox (norm_nonneg _))
          _ = _ := by ring
      have hs : ‖S w‖ ≤ q * ‖w‖ := by
        have h0 := (hcoer (S w)).trans (by simpa only [hS, ContinuousLinearMap.comp_apply] using ht)
        have h1 : ‖S w‖^2 ≤ (q * ‖w‖)^2 := by nlinarith
        nlinarith [norm_nonneg (S w), mul_nonneg hq.le (norm_nonneg w)]
      have hv : ‖w‖^2 ≤ ‖B‖ * ‖S w‖ * ‖v‖ := by
        calc
          _ = B (S w) v := (hS w v).trans hwJ |>.symm
          _ ≤ ‖B (S w) v‖ := le_abs_self _
          _ ≤ ‖B (S w)‖ * ‖v‖ := (B (S w)).le_opNorm v
          _ ≤ _ := mul_le_mul_of_nonneg_right (B.le_opNorm (S w)) (norm_nonneg _)
      have hv' : ‖w‖^2 ≤ (‖B‖ * q * ‖v‖) * ‖w‖ := by
        calc
          _ ≤ ‖B‖ * ‖S w‖ * ‖v‖ := hv
          _ ≤ ‖B‖ * (q * ‖w‖) * ‖v‖ := by gcongr
          _ = _ := by ring
      change ‖w‖ ≤ ‖B‖ * q * ‖v‖
      by_cases hw0 : ‖w‖ = 0
      · rw [hw0]; positivity
      · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
        rw [pow_two] at hv'
        exact (mul_le_mul_iff_left₀ hwpos).mp (by simpa only [mul_comm] using hv')
    rw [dist_eq_norm]
    have he : ‖B‖ * q < δ := by
      dsimp [q]
      have hd : 0 < 2 * (‖B‖ + 1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hd]
      nlinarith [norm_nonneg B]
    simpa only [norm_sub_rev] using ha.trans_lt he
  exact isClosed_setOfPred_isCompactOperator.closure_subset hcl

end StrictHotSpots.CompactCoercive
end CompactCoerciveCombinedLayer

section DiskCompactEmbeddingCombinedLayer
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private lemma boundedKernel_measurable : Measurable boundedKernel :=
  Measurable.ite (diskOpen.measurableSet.preimage measurable_fst) measurable_kernel measurable_const

private lemma compactRow_memLp : MemLp compactRow 2 (volume.restrict disk) := by
  let : MeasurableSpace (Lp ℝ 2 (volume.restrict disk)) := borel _
  let : BorelSpace (Lp ℝ 2 (volume.restrict disk)) := ⟨rfl⟩
  have hm : Measurable compactRow := CompactRows.measurable_toLp_rows boundedKernel
    boundedKernel_measurable boundedKernel_memLp
  apply MemLp.of_bound hm.aestronglyMeasurable kernel_bound.choose
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  rw [compactRow, Lp.norm_toLp]
  simpa only [boundedKernel, ite_eq_left hx] using kernel_bound.choose_spec.2 x hx



lemma integralOperator_compact : IsCompactOperator integralOperator := by
  let r := compactRow_memLp.toLp compactRow
  have he : integralOperator = CompactRows.rowOperator r := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [integralOperator_ae f, CompactRows.rowOperator_apply_ae r f,
      compactRow_memLp.coeFn_toLp, ae_restrict_mem diskOpen.measurableSet] with x hx hy hr hxd
    rw [hx,hy,hr,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(boundedKernel_memLp x).coeFn_toLp] with y hxy
    change kernel x y * f y = inner ℝ (f y) (compactRow x y)
    rw [RCLike.inner_apply]
    change kernel x y * f y = compactRow x y * f y
    congr 1
    have ht : compactRow x y = kernel x y := by
      simpa only [compactRow, boundedKernel, ite_eq_left hxd] using hxy
    exact ht.symm
  rw [he]
  exact CompactRows.rowOperator_compact r



lemma value_compact : IsCompactOperator (H10.value diskOpen) := by
  let B := H10.energy diskOpen
  let hB := H10.energy_coercive diskOpen diskBounded
  let J := H10.value diskOpen
  let S := DirichletOperator.solution B hB J
  apply CompactCoercive.observation_compact B hB J S
  · exact DirichletOperator.solution_spec B hB J
  · change IsCompactOperator variationalOperator
    rw [← integralOperator_eq_variationalOperator]
    exact integralOperator_compact

end StrictHotSpots.PlaneGreen
end DiskCompactEmbeddingCombinedLayer

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

lemma dense_smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (smoothTestToH10 hΩ) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : H1 Ω) ∈ closure (Set.range (smoothTestToH1 hΩ)) := u.property
  obtain ⟨v,⟨f,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  exact ⟨smoothTestToH10 hΩ f, ⟨f,rfl⟩, hv⟩

end StrictHotSpots
end H10InclusionCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Dirichlet
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10DilationCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots
open DiskH10

lemma smoothTest_value_sq_global {Ω : Set Plane} (hΩ : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.value hΩ (smoothTestToH10 hΩ f)‖^2 = ∫ x, ((f : Plane → ℝ) x)^2 := by
  rw [L2Limits.norm_sq_eq_integral_sq]
  have he : (∫ x in Ω, (H10.value hΩ (smoothTestToH10 hΩ f) x)^2) =
      ∫ x in Ω, ((f : Plane → ℝ) x)^2 := by
    apply integral_congr_ae
    filter_upwards [(test_memLp (Ω := Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
    exact congrArg (fun t : ℝ => t^2) hx
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (f.property.2.2 hh)),zero_pow (by norm_num : 2 ≠ 0)]

lemma smoothTest_grad_sq_global {Ω : Set Plane} (hΩ : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.grad hΩ (smoothTestToH10 hΩ f)‖^2 = ∫ x, ‖gradient (f : Plane → ℝ) x‖^2 := by
  rw [L2VectorLimits.norm_sq_eq_integral_norm_sq]
  have he : (∫ x in Ω, ‖H10.grad hΩ (smoothTestToH10 hΩ f) x‖^2) =
      ∫ x in Ω, ‖gradient (f : Plane → ℝ) x‖^2 := by
    apply integral_congr_ae
    filter_upwards [(test_gradient_memLp (Ω := Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
    exact congrArg (fun t : Plane => ‖t‖^2) hx
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [gradient,fderiv_of_notMem_tsupport ℝ (fun hh => hx (f.property.2.2 hh)),map_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]

lemma gradient_comp_smul {f : Plane → ℝ} (hf : Differentiable ℝ f) (R : ℝ) (x : Plane) :
    gradient (fun y => f (R • y)) x = R • gradient (f : Plane → ℝ) (R • x) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hd : fderiv ℝ (fun y : Plane => f (R • y)) x =
    (fderiv ℝ (f : Plane → ℝ) (R • x)).comp (R • ContinuousLinearMap.id ℝ Plane) :=
    (hf (R • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R) |>.fderiv
  rw [hd]
  simp

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

lemma dilateTest_value_sq (f : smoothTestSpace Ω) :
    ‖value PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))‖^2 =
      (R^2)⁻¹ * ‖value hΩ (smoothTestToH10 hΩ f)‖^2 := by
  rw [smoothTest_value_sq_global,smoothTest_value_sq_global]
  change (∫ x : Plane, ((f : Plane → ℝ) (R • x))^2) = _
  have := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) (fun x => ((f : Plane → ℝ) x)^2) R
    (hR := (radius_pos hR).le)
  simpa [Plane, finrank_euclideanSpace, smul_eq_mul] using this

lemma dilateTest_grad_sq (f : smoothTestSpace Ω) :
    ‖grad PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))‖^2 =
      ‖grad hΩ (smoothTestToH10 hΩ f)‖^2 := by
  rw [smoothTest_grad_sq_global,smoothTest_grad_sq_global]
  have hd : ∀ x, gradient (dilateTest hR hb f : Plane → ℝ) x = R • gradient (f : Plane → ℝ) (R • x) :=
    gradient_comp_smul (f.property.1.differentiable (by simp)) R
  simp_rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (radius_pos hR),mul_pow]
  rw [integral_const_mul]
  have ht := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
    (fun x => ‖gradient (f : Plane → ℝ) x‖^2) R (hR := (radius_pos hR).le)
  simp only [Plane, finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul] at ht
  rw [ht]
  field_simp [(radius_pos hR).ne']

lemma dilateTest_norm (f : smoothTestSpace Ω) :
    ‖smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f)‖ ≤ ‖smoothTestToH10 hΩ f‖ := by
  have ha := dilateTest_value_sq hΩ hR hb f
  have hg := dilateTest_grad_sq hΩ hR hb f
  have hnorm1 := norm_sq PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))
  have hnorm2 := norm_sq hΩ (smoothTestToH10 hΩ f)
  have hi : (R^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hs := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖value hΩ (smoothTestToH10 hΩ f)‖)
  nlinarith [norm_nonneg (smoothTestToH10 hΩ f),norm_nonneg (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))]

end H10
end StrictHotSpots
end H10DilationCombinedLayer

section CompactDominationCombinedLayer
open Set Metric
namespace StrictHotSpots
lemma compact_of_norm_dominated {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : E →L[ℝ] F) (K : E →L[ℝ] G) (hK : IsCompactOperator K)
    {C : ℝ} (hC : 0 < C) (h : ∀ x, ‖J x‖ ≤ C * ‖K x‖) : IsCompactOperator J := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall J.toLinearMap zero_lt_one).mpr
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have ht : TotallyBounded (K '' closedBall 0 1) :=
    (hK.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  obtain ⟨t,htsub,htfin,hcover⟩ := Metric.finite_approx_of_totallyBounded ht
    (ε / C) (div_pos hε hC)
  choose x hxball hx using fun y : t => htsub y.property
  let : Finite t := htfin.to_subtype
  refine ⟨Set.range (fun y : t => J (x y)), Set.finite_range _, ?_⟩
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨y,hy,hyv⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem K hv))
  refine mem_iUnion₂.mpr ⟨J (x ⟨y,hy⟩),mem_range_self _,?_⟩
  rw [mem_ball,dist_eq_norm]
  change ‖J v - J (x ⟨y,hy⟩)‖ < ε
  rw [← J.map_sub]
  apply (h (v-x ⟨y,hy⟩)).trans_lt
  rw [map_sub,hx]
  have hh : ‖K v - y‖ < ε / C := by simpa only [Metric.mem_ball, dist_eq_norm] using hyv
  have := (lt_div_iff₀ hC).mp hh
  simpa only [mul_comm] using this
end StrictHotSpots
end CompactDominationCombinedLayer

section BoundedCompactEmbeddingCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
open DiskH10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

lemma dilation_test (f : smoothTestSpace Ω) :
    dilation hΩ hR hb (smoothTestToH10 hΩ f) =
      smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 hΩ)
    ⟨1,fun f => by
      rw [one_mul]
      exact dilateTest_norm hΩ hR hb f⟩ f

lemma dilation_value_sq (u : H10 hΩ) :
    ‖value PlaneGreen.diskOpen (dilation hΩ hR hb u)‖^2 =
      (R^2)⁻¹ * ‖value hΩ u‖^2 := by
  apply isClosed_property (dense_smoothTestToH10 hΩ) _ _ u
  · exact isClosed_eq (((value PlaneGreen.diskOpen).continuous.comp
      (dilation hΩ hR hb).continuous).norm.pow 2)
      (continuous_const.mul ((value hΩ).continuous.norm.pow 2))
  · intro f
    rw [dilation_test]
    exact dilateTest_value_sq hΩ hR hb f

private lemma le_mul_of_inv_sq {a b R : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : 0 < R) (h : b^2 = (R^2)⁻¹ * a^2) : a ≤ R * b := by
  have he : R^2 * b^2 = a^2 := by rw [h]; field_simp
  nlinarith [mul_nonneg hR.le hb]

lemma value_dilation_bound (u : H10 hΩ) :
    ‖value hΩ u‖ ≤ R * ‖value PlaneGreen.diskOpen (dilation hΩ hR hb u)‖ :=
  le_mul_of_inv_sq (norm_nonneg _) (norm_nonneg _) (zero_lt_one.trans_le hR)
    (dilation_value_sq hΩ hR hb u)

include hR hb in
lemma value_compact_of_ball : IsCompactOperator (value hΩ) := by
  let K : H10 hΩ →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
    (value PlaneGreen.diskOpen).comp (dilation hΩ hR hb)
  have hK : IsCompactOperator K := PlaneGreen.value_compact.comp_clm (dilation hΩ hR hb)
  exact compact_of_norm_dominated (value hΩ) K hK (zero_lt_one.trans_le hR)
    (value_dilation_bound hΩ hR hb)

include hΩ in
lemma value_compact (hbounded : Bornology.IsBounded Ω) : IsCompactOperator (value hΩ) := by
  obtain ⟨r,hr⟩ := hbounded.subset_ball (0 : Plane)
  exact value_compact_of_ball hΩ (le_max_left 1 r)
    (hr.trans (Metric.ball_subset_ball (le_max_right 1 r)))

end StrictHotSpots.H10
end BoundedCompactEmbeddingCombinedLayer

section PositiveCompactCombinedLayer
open Set
open scoped InnerProductSpace
namespace StrictHotSpots

lemma positive_norm_mem_spectrum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℝ] H) (hs : T.IsSymmetric) (hp : ∀ x, 0 ≤ inner ℝ (T x) x) :
    ‖T‖ ∈ spectrum ℝ T := by
  by_contra h
  have hr : algebraMap ℝ ℝ ‖T‖ ∈ resolventSet ℝ T := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (not_not.mp h)
  obtain ⟨ε,hε,hgap⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hr
  have hn := T.norm_eq_iSup_rayleighQuotient hs
  have hbound : ‖T‖ ≤ ‖T‖ - ε := by
    calc
      ‖T‖ = ⨆ x, |T.rayleighQuotient x| := hn
      _ ≤ ‖T‖ - ε := by
        apply ciSup_le
        intro x
        have hx : 0 ≤ T.rayleighQuotient x := by
          exact div_nonneg (hp x) (sq_nonneg _)
        rw [abs_of_nonneg hx]
        exact hgap x
  linarith

lemma positive_compact_top_eigenvector {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hs : T.IsSymmetric) (hp : ∀ x, 0 ≤ inner ℝ (T x) x)
    (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ f : H, f ≠ 0 ∧ T f = ‖T‖ • f := by
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro hh
    apply hne
    ext x
    exact Subsingleton.elim _ _)
  have he := (hc.hasEigenvalue_iff_mem_spectrum (norm_ne_zero_iff.mpr hne)).mpr
    (positive_norm_mem_spectrum T hs hp)
  obtain ⟨f,hf⟩ := he.exists_hasEigenvector
  exact ⟨f,hf.2,Module.End.mem_eigenspace_iff.mp hf.1⟩

end StrictHotSpots
end PositiveCompactCombinedLayer

section DirichletAttainmentCombinedLayer
open Set
open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] in
lemma energy_nonneg (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (v : V) :
    0 ≤ B v v := by
  obtain ⟨C,hC,h⟩ := hB
  exact (mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (norm_nonneg _)).trans (h v)

omit [CompleteSpace V] in
lemma energy_eq_zero (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) {v : V}
    (h : B v v = 0) : v = 0 := by
  obtain ⟨C,hC,hc⟩ := hB
  have hh := hc v
  rw [h] at hh
  have : ‖v‖ = 0 := le_antisymm (le_of_not_gt (fun hv =>
    (not_lt_of_ge hh) (mul_pos (mul_pos hC hv) hv))) (norm_nonneg v)
  exact norm_eq_zero.mp this

lemma green_ne_zero (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (hJ : J ≠ 0) : green B hB J ≠ 0 := by
  intro h
  apply hJ
  ext v
  have hS : solution B hB J (J v) = 0 := by
    apply energy_eq_zero B hB
    rw [solution_spec, ← green_apply, h, zero_apply, inner_zero_right]
  have ht := solution_spec B hB J (J v) v
  rw [hS, map_zero, zero_apply, real_inner_self_eq_norm_sq] at ht
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (J v)])



lemma minimum_attained (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ u v, B u v = B v u) (J : V →L[ℝ] H)
    (hJ : J ≠ 0) (hc : IsCompactOperator J) :
    ∃ (lam : ℝ) (φ : V), 0 < lam ∧ J φ ≠ 0 ∧
      (∀ v, lam * ‖J v‖^2 ≤ B v v) ∧
      (∀ v, B φ v = lam * inner ℝ (J φ) (J v)) := by
  let T := green B hB J
  have hT : T ≠ 0 := green_ne_zero B hB J hJ
  have hθ : 0 < ‖T‖ := norm_pos_iff.mpr hT
  obtain ⟨f,hf,he⟩ := positive_compact_top_eigenvector T
    (green_symmetric B hB hsym J) (fun f => by
      rw [real_inner_comm]; exact green_nonneg B hB J f)
    (hc.comp_clm (solution B hB J)) hT
  let φ := solution B hB J f
  have hφ : J φ = ‖T‖ • f := he
  refine ⟨‖T‖⁻¹,φ,inv_pos.mpr hθ,?_,?_,?_⟩
  · rw [hφ]
    exact smul_ne_zero hθ.ne' hf
  · intro v
    let w := solution B hB J (J v)
    have hw : B w v = ‖J v‖^2 := by
      rw [solution_spec, real_inner_self_eq_norm_sq]
    have hw' : B v w = ‖J v‖^2 := (hsym v w).trans hw
    have hww : B w w ≤ ‖T‖ * ‖J v‖^2 := by
      calc
        _ = inner ℝ (J v) (T (J v)) := solution_spec B hB J (J v) w
        _ ≤ ‖J v‖ * ‖T (J v)‖ := real_inner_le_norm _ _
        _ ≤ ‖J v‖ * (‖T‖ * ‖J v‖) := by
          gcongr; exact T.le_opNorm _
        _ = _ := by ring
    have hpos := energy_nonneg B hB (‖T‖ • v - w)
    simp only [map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul] at hpos
    rw [hw,hw'] at hpos
    have hineq : ‖J v‖^2 ≤ ‖T‖ * B v v := by nlinarith
    rw [inv_mul_eq_div, div_le_iff₀ hθ]
    nlinarith
  · intro v
    rw [solution_spec, hφ, real_inner_smul_left]
    field_simp

end StrictHotSpots.DirichletOperator
end DirichletAttainmentCombinedLayer

section DirichletMinimumCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma value_ne_zero (hne : Ω.Nonempty) : value hΩ ≠ 0 := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨f,hs,hc,hf,_,hfa⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hΩ.mem_nhds ha)
  let t : smoothTestSpace Ω := ⟨f,hf,hc,hs⟩
  intro hz
  have he : (test_memLp (Ω := Ω) hf hc).toLp f = 0 := by
    change value hΩ (smoothTestToH10 hΩ t) = 0
    exact DFunLike.congr_fun hz (smoothTestToH10 hΩ t)
  have hae : f =ᵐ[volume.restrict Ω] (fun _ => (0 : ℝ)) :=
    (test_memLp hf hc).coeFn_toLp.symm.trans (he ▸ Lp.coeFn_zero _ _ _)
  have hp := Measure.eqOn_open_of_ae_eq hae hΩ hf.continuous.continuousOn continuousOn_const ha
  exact zero_ne_one (hp.symm.trans hfa)



lemma minimum_oai (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ (lam : ℝ) (φ : H10 hΩ), 0 < lam ∧ value hΩ φ ≠ 0 ∧
      (∀ v, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2) ∧
      (∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
        lam * inner ℝ (value hΩ φ) (value hΩ v)) := by
  have hsym : ∀ u v : H10 hΩ, energy hΩ u v = energy hΩ v u := by
    intro u v
    exact (real_inner_comm (grad hΩ u) (grad hΩ v)).symm
  have hm := @DirichletOperator.minimum_attained (H10 hΩ) (Lp ℝ 2 (volume.restrict Ω))
    (H10.normedAddCommGroup hΩ) (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    inferInstance inferInstance inferInstance (energy hΩ) (energy_coercive hΩ hb)
    hsym (value hΩ) (value_ne_zero hΩ hne) (value_compact hΩ hb)
  obtain ⟨lam,φ,hl,hφ,hineq,heq⟩ := hm
  refine ⟨lam,φ,hl,hφ,?_,heq⟩
  intro v
  simpa only [energy_apply,real_inner_self_eq_norm_sq] using hineq v

end StrictHotSpots.H10
end DirichletMinimumCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.H10.minimum_oai := @OAI.StrictHotSpots.H10.minimum_oai
