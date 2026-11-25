-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:09.586269+00:00
-- url     : https://prove2.me/submissions/81e5c884-a7f7-4a89-8533-de56e45c7843

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : ℕ) : axExponent p k ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have h1 := one_lt_prime_cast (p := p)
  have hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ ((p : ℝ) ^ k)⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) _)
  unfold axExponent
  nlinarith
end GroundTheory.PAdicHodge
