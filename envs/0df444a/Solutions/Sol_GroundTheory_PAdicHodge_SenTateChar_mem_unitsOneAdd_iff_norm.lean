-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.mem_unitsOneAdd_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:15.870959+00:00
-- url     : https://prove2.me/submissions/43f9a551-6602-4897-8294-9a3aacce087c

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
theorem _root_.solution {k : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsOneAdd p k ↔ ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [mem_unitsOneAdd, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
end GroundTheory.PAdicHodge.SenTateChar
