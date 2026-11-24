-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VectorTaylor.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:12.167381+00:00
-- url     : https://prove2.me/submissions/962d2b1e-7ad5-400a-aff9-3e1d40772094

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_factorial_add_le
import Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_iter_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology
namespace GlobalTheory.CompanionTheory.VectorTaylor
theorem _root_.solution (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0)
    (s : ℝ) (hs : |s| ≤ 1 / (4 * D)) (k : ℕ) : f k (t₀ + s) = 0 := by
  have hD0 : 0 < D := by linarith
  have h2Ds : 2 * D * |s| ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * D)
    calc 2 * D * |s| ≤ 2 * D * (1 / (4 * D)) := h
      _ = 1 / 2 := by field_simp; ring
  have hbound : ∀ n : ℕ, ‖f k (t₀ + s)‖ ≤ B * (2 * D) ^ k * k.factorial * (1 / 2) ^ n := by
    intro n
    have hA := iter_bound f (fun k => B * D ^ k * (k.factorial : ℝ)) hd hb t₀ h0 n k s
    have hfact := factorial_add_le k n
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    calc ‖f k (t₀ + s)‖ ≤ B * D ^ (k + n) * ((k + n).factorial : ℝ) * |s| ^ n / n.factorial := hA
      _ ≤ B * D ^ (k + n) * (2 ^ (k + n) * k.factorial * n.factorial) * |s| ^ n / n.factorial := by
          gcongr
      _ = B * (2 * D) ^ k * k.factorial * (2 * D * |s|) ^ n := by
          field_simp
          ring
      _ ≤ B * (2 * D) ^ k * k.factorial * (1 / 2) ^ n := by
          gcongr
  have hlim : Tendsto (fun n : ℕ => B * (2 * D) ^ k * k.factorial * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (B * (2 * D) ^ k * k.factorial)
  have hle : ‖f k (t₀ + s)‖ ≤ 0 := ge_of_tendsto' hlim hbound
  exact norm_le_zero_iff.mp hle
end GlobalTheory.CompanionTheory.VectorTaylor
