-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.hasSum_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:35.11937+00:00
-- url     : https://prove2.me/submissions/ab8803da-9ed6-46c9-8b93-6e5f045cc163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_row
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s))
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h : Summable fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s) :=
    (summable_prod_of_nonneg fun p => by positivity).2
      ⟨summable_row x hy hs.le, (hasSum_rows x hy hs).summable⟩
  rw [← (hasSum_rows x hy hs).tsum_eq]
  exact h.tsum_prod ▸ h.hasSum
end GlobalTheory.KroneckerLimit
