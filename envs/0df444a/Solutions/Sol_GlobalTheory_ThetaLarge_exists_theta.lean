-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:32.970271+00:00
-- url     : https://prove2.me/submissions/e7a3ba6e-a06c-4145-845c-d239b9878d6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
import Theorems.Thm_GlobalTheory_ThetaLarge_term_add
import Theorems.Thm_GlobalTheory_ThetaLarge_norm_term
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal
import Theorems.Thm_GlobalTheory_exp_neg_mul_norm_add_sq_le
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {E : Type*} [NormedAddCommGroup E]
variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}
namespace GlobalTheory.ThetaLarge
theorem _root_.solution [NormedSpace ℂ E] [FiniteDimensional ℂ E] [DiscreteTopology L]
    [DecidableEq L] (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (hd : ∀ w, Differentiable ℂ fun z => H z w) (hc : Continuous fun z => (H z z).re)
    {a : ℝ} (ha : 0 < a) (hsum : ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1)
    (hH : ∀ z, a * ‖z‖ ^ 2 ≤ π / 2 * (H z z).re) (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im)) (z₀ : E) :
    ∃ θ : E → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : L) z,
      θ (z + l) = (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * θ z := by
  have hle : ∀ (l : L) z, ‖term L H χ z₀ l z‖ ≤ Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-a * ‖(l : E) + (z - z₀)‖ ^ 2) := fun l z => by
    rw [norm_term hl hr hs h1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    linarith [hH (l + (z - z₀))]
  refine ⟨fun z => ∑' l : L, term L H χ z₀ l z, ?_, ?_, fun l z => ?_⟩
  · rw [← differentiableOn_univ]
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun l => ?_) (fun x _ => ?_)
    · have h2 : Differentiable ℂ fun z : E => H (z + l) z₀ :=
        (hd z₀).comp (differentiable_id.add_const _)
      have h3 := hd l
      unfold term
      refine Differentiable.differentiableOn ?_
      fun_prop
    · have hx : ∀ᶠ z in 𝓝 x, (H z z).re < (H x x).re + 1 ∧ ‖z - z₀‖ < ‖x - z₀‖ + 1 :=
        (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).and
          ((show Continuous fun z : E => ‖z - z₀‖ by fun_prop).continuousAt.eventually
            (gt_mem_nhds (lt_add_one _)))
      refine ⟨_, hx, _, ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left
        (Real.exp (a * (‖x - z₀‖ + 1) ^ 2))).mul_left
        (Real.exp (π / 2 * ((H x x).re + 1 + (H z₀ z₀).re))), fun l z hz => (hle l z).trans ?_⟩
      refine mul_le_mul ?_ (exp_neg_mul_norm_add_sq_le ha.le _ hz.2.le) (Real.exp_pos _).le
        (Real.exp_pos _).le
      gcongr
      exact hz.1.le
  · set A := Real.exp (π / 2 * ((H z₀ z₀).re + (H z₀ z₀).re)) with hA
    have hA0 : 0 < A := Real.exp_pos _
    have hle' : ∀ l : L, ‖term L H χ z₀ l z₀‖ ≤ A * Real.exp (-a * ‖(l : E)‖ ^ 2) := fun l => by
      simpa using hle l z₀
    have hg := summable_lattice_exp_neg_mul_norm_sq L ha
    have hS : Summable fun l : L => term L H χ z₀ l z₀ :=
      .of_norm_bounded (hg.mul_left A) hle'
    have h00 : H 0 0 = 0 := by simpa using hl 0 0 0
    have h0 : ‖term L H χ z₀ 0 z₀‖ = A := by
      rw [norm_term hl hr hs h1]
      simp [h00, hA]
    have hg' : Summable fun l : L => if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2) :=
      .of_nonneg_of_le (fun l => by split_ifs <;> positivity)
        (fun l => by split_ifs <;> [positivity; rfl]) hg
    have h2 : ‖∑' l : L, if l = 0 then 0 else term L H χ z₀ l z₀‖ ≤
        A * ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) := by
      refine tsum_of_norm_bounded (hg'.hasSum.mul_left A) fun l => ?_
      split_ifs
      · simp
      · exact hle' l
    intro h
    beta_reduce at h
    rw [hS.tsum_eq_add_tsum_ite 0, add_eq_zero_iff_eq_neg] at h
    rw [h, norm_neg] at h0
    nlinarith
  · beta_reduce
    rw [← (Equiv.addLeft l).tsum_eq fun m => term L H χ z₀ m z, ← tsum_mul_left]
    exact tsum_congr fun m => term_add hl hr hs h1 hχ z₀ l m z
end GlobalTheory.ThetaLarge
