-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.pow_prime_pow_mem_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:05.11252+00:00
-- url     : https://prove2.me/submissions/3a69d893-92b7-4fed-aa0c-582adb79c82e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_pow_prime_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution {s : ℕ} (hs : 2 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) (i : ℕ) :
    a ^ p ^ i ∈ unitsOneAdd p (s + i) ∧ a ^ p ^ i ∉ unitsOneAdd p (s + i + 1) := by
  induction i with
  | zero => simpa using ⟨ha, ha'⟩
  | succ i ih =>
    have h := pow_prime_mem_iff (by omega : 2 ≤ s + i) ih.1
    rw [pow_succ, pow_mul]
    refine ⟨by simpa [add_assoc] using h.1, fun hc => ih.2 (h.2.1 ?_)⟩
    simpa [add_assoc] using hc
end GroundTheory.PAdicHodge.SenTateChar
