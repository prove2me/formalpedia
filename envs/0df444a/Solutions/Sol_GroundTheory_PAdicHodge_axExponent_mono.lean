-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axExponent_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:58.240959+00:00
-- url     : https://prove2.me/submissions/4076d005-6418-40d7-9e96-8b5311dd4825

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
theorem _root_.solution {j k : ℕ} (h : j ≤ k) : axExponent p j ≤ axExponent p k := by
  have h1 := one_lt_prime_cast (p := p)
  have hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have h2 : ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_right₀ h1.le h)
  unfold axExponent
  exact mul_le_mul_of_nonneg_left (by linarith) hC
end GroundTheory.PAdicHodge
