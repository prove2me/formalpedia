-- Prove2me | solution 1 for GlobalTheory.SharpGradient.sharpAt_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:29.102858+00:00
-- url     : https://prove2.me/submissions/d09248e8-365a-41b8-a1cf-b957390bc8cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_normSq_sum_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.SharpGradient
theorem _root_.solution {m : ℕ} {g : Fin m → V n → ℂ} {x : V n} (ξ : Fin n → ℂ)
    (hg : ∀ i, ContDiffAt ℂ 2 (g i) x) (hlt : ∑ i, Complex.normSq (g i x) < 1) :
    SharpAt (fun y => -Real.log (1 - ∑ i, Complex.normSq (g i y))) x ξ := by
  set k : ℝ → ℝ := fun t => -Real.log (1 - t) with hk
  have hu : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (g i y)) x := fun i =>
    H.contDiffAt_normSq_comp (hg i)
  have hS : ContDiffAt ℝ 2 (fun y => ∑ i, Complex.normSq (g i y)) x :=
    ContDiffAt.sum fun i _ => hu i
  set t := ∑ i, Complex.normSq (g i x) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h1t : 0 < 1 - t := by linarith
  have hkc : ContDiffAt ℝ 2 k t := by
    refine ContDiffAt.neg ?_
    exact (Real.contDiffAt_log.2 h1t.ne').comp t (contDiffAt_const.sub contDiffAt_id)
  have hd1 : deriv k = fun s => (1 - s)⁻¹ := by
    funext s
    simp only [hk]
    rw [deriv.fun_neg, deriv_comp_const_sub Real.log, Real.deriv_log, neg_neg]
  have hd2 : deriv (deriv k) t = ((1 - t) ^ 2)⁻¹ := by
    rw [hd1, deriv_comp_const_sub (fun s : ℝ => s⁻¹), deriv_inv, neg_neg]
  have hc := H.leviChain n k (fun y => ∑ i, Complex.normSq (g i y)) x ξ hS hkc
  set η : Fin m → ℂ := fun i => ∑ j, wd n j (g i) x * ξ j with hη
  have hw : ∑ j, wd n j (fun y => ((∑ i, Complex.normSq (g i y) : ℝ) : ℂ)) x * ξ j =
      ∑ i, η i * conj (g i x) := by
    simp only [hη, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
      (fun i => (hu i).differentiableAt (by simp)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [H.wd_normSq_comp (hg i)]; ring
  rw [H.leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y)) hu, hw, ← ht, hd2, hd1] at hc
  simp only [fun i => H.leviV_normSq_comp (hg i) ξ] at hc
  set N := Complex.normSq (∑ i, η i * conj (g i x)) with hN
  set M := ∑ i, Complex.normSq (η i) with hM
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hNM : N ≤ M * t := by
    refine normSq_sum_le _ _ _ (fun i => Complex.normSq_nonneg _)
      (fun i => Complex.normSq_nonneg _) fun i => ?_
    rw [Complex.normSq_mul, Complex.normSq_conj]
  have hL : (leviV n (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x ξ).re =
      (1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N := by
    have : leviV n (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x ξ =
        (((1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N : ℝ) : ℂ) := by
      refine hc.trans ?_
      simp only [hM, hη, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum]
    rw [this, Complex.ofReal_re]
  have hG : ∑ j, wd n j (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x * ξ j
      = (((1 - t)⁻¹ : ℝ) : ℂ) * ∑ i, η i * conj (g i x) := by
    rw [← hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := wd_ofReal_comp (j := j) (k := k) (v := fun y => ∑ i, Complex.normSq (g i y)) (x := x)
      (hkc.differentiableAt (by simp)) (hS.differentiableAt (by simp))
    rw [hd1] at this
    rw [← mul_assoc, ← this]
  have hlog : t ≤ -Real.log (1 - t) := by
    have := Real.log_le_sub_one_of_pos h1t
    linarith
  have hi : 0 < (1 - t)⁻¹ := inv_pos.2 h1t
  have hL0 : 0 ≤ (1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N := by positivity
  have hcc : ContDiffAt ℝ 2 (k ∘ fun y => ∑ i, Complex.normSq (g i y)) x := hkc.comp x hS
  refine ⟨hcc, ht0.trans hlog, hL ▸ hL0, ?_⟩
  rw [hL, hG, Complex.normSq_mul, Complex.normSq_ofReal, ← hN]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hlog hL0)
  have e : t * ((1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N) - (1 - t)⁻¹ * (1 - t)⁻¹ * N =
      (1 - t)⁻¹ * (M * t - N) := by
    field_simp
    ring
  have : 0 ≤ (1 - t)⁻¹ * (M * t - N) := mul_nonneg hi.le (by linarith)
  linarith
end GlobalTheory.SharpGradient
