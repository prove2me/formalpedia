-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.eq_one_of_forall_mem_unitsOneAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:14.795448+00:00
-- url     : https://prove2.me/submissions/abd5e4dd-d3b8-42b0-9b30-eebbad5e60d3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits

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
theorem _root_.solution {u : ℤ_[p]ˣ} (hu : ∀ k, u ∈ unitsOneAdd p k) : u = 1 := by
  by_contra hne
  have h0 : (u : ℤ_[p]) - 1 ≠ 0 := by
    intro h; apply hne; ext; simpa [sub_eq_zero] using h
  have h := (PadicInt.mem_span_pow_iff_le_valuation _ h0 (((u : ℤ_[p]) - 1).valuation + 1)).1
    (Ideal.mem_span_singleton.2 (hu _))
  omega
end GroundTheory.PAdicHodge.SenTateChar
