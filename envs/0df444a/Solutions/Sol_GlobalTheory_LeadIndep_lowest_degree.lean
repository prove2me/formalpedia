-- Prove2me | solution 1 for GlobalTheory.LeadIndep.lowest_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:54.923795+00:00
-- url     : https://prove2.me/submissions/0309e321-8fa7-440f-b034-2ea9607605cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadMCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.LeadIndep
open Filter
private theorem sum_mul_pow_mul_prod_eq_div_pow {n δ : ℕ} (α : Fin n → ℕ) (c : Fin δ → ℂ) (Φv : Fin δ → ℂ)
    (σv : Fin n → ℂ) (w t : ℂ) (T d : ℕ) (ht : t ≠ 0) (hw : w ≠ 0)
    (hle : (∃ k, c k ≠ 0) → d ≤ ∑ q, α q) :
    (∑ k, c k * Φv k) * t ^ (∑ q, α q - d) * w ^ (∑ q, α q + (T - ∑ q, α q)) *
        ∏ q, (t⁻¹ * (σv q / w)) ^ α q =
      (∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k) / t ^ d := by
  by_cases hz : ∀ k, c k = 0
  · simp [hz]
  push Not at hz
  have hd := hle hz
  have hprod : ∏ q, (t⁻¹ * (σv q / w)) ^ α q = (t⁻¹ * w⁻¹) ^ (∑ q, α q) * ∏ q, σv q ^ α q := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← mul_pow, div_eq_mul_inv]
    ring
  have hsum : ∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k =
      (∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hprod, hsum]
  generalize ∑ q, α q = s at hd ⊢
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [Nat.add_sub_cancel_left, eq_div_iff (pow_ne_zero d ht)]
  have key : (t⁻¹ * w⁻¹) ^ (d + e) * (t * w) ^ (d + e) = 1 := by
    rw [← mul_pow, show t⁻¹ * w⁻¹ * (t * w) = 1 by field_simp, one_pow]
  linear_combination ((∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - (d + e))) * key
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.LeadIndep
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeadIndep
open Filter
namespace GlobalTheory.LeadIndep
theorem _root_.solution {n δ : ℕ} (U : Set (V n)) (hU : IsOpen U)
    (vP : V n) (hvP : vP ∈ U) (σ : Fin n → V n → ℂ) (wz : V n → ℂ) (Φ : Fin δ → V n → ℂ)
    (M : Finset (Fin n → ℕ)) (T m d : ℕ) (c : (Fin n → ℕ) → Fin δ → ℂ)
    (hσ : ∀ k, DifferentiableOn ℂ (σ k) U) (hw : DifferentiableOn ℂ wz U)
    (hΦ : ∀ k, DifferentiableOn ℂ (Φ k) U)
    (hσ0 : ∀ k, σ k vP = 0) (hw0 : wz vP ≠ 0)
    (hlow : ∀ α ∈ M, ∀ k, c α k ≠ 0 → d ≤ ∑ q, α q) (hdm : d < m)
    (hb : ∃ C : ℝ, ∀ᶠ v in 𝓝 vP, ‖∑ α ∈ M, ∑ k,
      c α k * (∏ q, σ q v ^ α q) * wz v ^ (T - ∑ q, α q) * Φ k v‖ ≤ C * ‖v - vP‖ ^ m)
    (h0 : V n) :
    ∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
      ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q = 0 := by
  classical
  have hUn : U ∈ 𝓝 vP := hU.mem_nhds hvP
  have hwd : DifferentiableAt ℂ wz vP := hw.differentiableAt hUn
  have hΦc : ∀ k, ContinuousAt (Φ k) vP := fun k => ((hΦ k).differentiableAt hUn).continuousAt
  have hFd : DifferentiableAt ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP := by
    have h1 : DifferentiableAt ℂ (fun v => fun k => σ k v / wz v) vP :=
      differentiableAt_pi.2 fun k => by
        simpa only [div_eq_mul_inv, Function.comp_def, Pi.mul_def] using
          ((hσ k).differentiableAt hUn).mul ((differentiableAt_inv hw0).comp vP hwd)
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiableAt.comp vP h1
  have hl : HasDerivAt (fun t : ℂ => vP + t • h0) h0 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h0).const_add vP
  have hl0 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝 0) (𝓝 vP) := by
    simpa using hl.continuousAt.tendsto
  have hl1 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝[≠] 0) (𝓝 vP) := hl0.mono_left nhdsWithin_le_nhds
  have hFl : HasDerivAt (fun t : ℂ => (WithLp.toLp 2
      (fun k => σ k (vP + t • h0) / wz (vP + t • h0)) : V n))
      (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) 0 := by
    have hF' : HasFDerivAt (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n))
        (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP) (vP + (0 : ℂ) • h0) := by
      rw [zero_smul, add_zero]
      exact hFd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hcomp : ∀ q, Tendsto (fun t : ℂ => t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) (𝓝[≠] 0)
      (𝓝 ((fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) q)) := by
    intro q
    have h2 := ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) q).tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.1 hFl)
    refine h2.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, hσ0]
  have hlim : Tendsto (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) (𝓝[≠] 0)
      (𝓝 (∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q)) := by
    refine tendsto_finsetSum _ fun α _ => ?_
    refine Tendsto.mul (Tendsto.mul (Tendsto.mul ?_ ?_) ?_) ?_
    · exact tendsto_finsetSum _ fun k _ => ((hΦc k).tendsto.comp hl1).const_mul _
    · exact ((continuous_pow _).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · exact (hwd.continuousAt.tendsto.comp hl1).pow _
    · exact tendsto_finsetProd _ fun q _ => (hcomp q).pow _
  have hwne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), wz (vP + t • h0) ≠ 0 :=
    (hwd.continuousAt.tendsto.comp hl1).eventually_ne hw0
  have heq : (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) =ᶠ[𝓝[≠] 0]
      (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) := by
    filter_upwards [hwne, self_mem_nhdsWithin] with t hwt ht
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sum_mul_pow_mul_prod_eq_div_pow α (c α) (fun k => Φ k (vP + t • h0)) (fun q => σ q (vP + t • h0))
      (wz (vP + t • h0)) t T d ht hwt (fun ⟨k, hk⟩ => hlow α hα k hk)]
  obtain ⟨C, hC⟩ := hb
  have hzero : Tendsto (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) (𝓝[≠] 0) (𝓝 0) := by
    have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖(∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d‖ ≤
        C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) := by
      filter_upwards [hl1.eventually hC, self_mem_nhdsWithin] with t h1 ht
      have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
      rw [add_sub_cancel_left, norm_smul] at h1
      rw [norm_div, norm_pow, div_le_iff₀ (pow_pos htn d)]
      calc _ ≤ C * (‖t‖ * ‖h0‖) ^ m := h1
        _ = C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) * ‖t‖ ^ d := by
          rw [mul_pow, show ‖t‖ ^ m = ‖t‖ ^ (m - d) * ‖t‖ ^ d by
            rw [← pow_add, Nat.sub_add_cancel hdm.le]]
          ring
    refine squeeze_zero_norm' hbd ?_
    have h3 : Tendsto (fun t : ℂ => C * ‖h0‖ ^ m * ‖t‖ ^ (m - d)) (𝓝 0) (𝓝 (C * ‖h0‖ ^ m * ‖(0 : ℂ)‖ ^ (m - d))) :=
      ((continuous_norm.pow _).const_mul _).tendsto 0
    rw [norm_zero, zero_pow (Nat.sub_ne_zero_of_lt hdm), mul_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim (hzero.congr' heq)
end GlobalTheory.LeadIndep
