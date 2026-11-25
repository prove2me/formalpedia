-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axExponent_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:11.01531+00:00
-- url     : https://prove2.me/submissions/eb62506b-8c59-48e1-bce7-603ce76c8b7a

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
theorem _root_.solution (k : ℕ) :
    axExponent p (k + 1) = axExponent p k + 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
  have h1 := one_lt_prime_cast (p := p)
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  have h4 : (p : ℝ) ≠ 0 := by linarith
  simp only [axExponent, pow_succ]
  field_simp
  ring
end GroundTheory.PAdicHodge
