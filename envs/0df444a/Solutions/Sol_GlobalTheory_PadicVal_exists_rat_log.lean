-- Prove2me | solution 1 for GlobalTheory.PadicVal.exists_rat_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:46.012924+00:00
-- url     : https://prove2.me/submissions/44103dbf-1071-48e5-9baa-e62808a34212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.PadicVal
theorem _root_.solution (x : PadicAlgCl p) (hx : x ≠ 0) : ∃ q : ℚ, Real.log ‖x‖ = q * Real.log p := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hn : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨((-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ) : ℚ) / ((minpoly ℚ_[p] x).natDegree : ℚ), ?_⟩
  rw [hn, Real.log_rpow (norm_pos_iff.2 hc), Padic.norm_eq_zpow_neg_valuation hc, Real.log_zpow]
  push_cast
  ring
end GlobalTheory.PadicVal
