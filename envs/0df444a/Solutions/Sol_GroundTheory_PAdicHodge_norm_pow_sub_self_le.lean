-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_sub_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:04.462901+00:00
-- url     : https://prove2.me/submissions/fda7d4c6-6b3b-45a9-b77a-73f31cfe4fec

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm

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
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : ‖c ^ p - c‖ ≤ (p : ℝ)⁻¹ := by
  set b : ℤ_[p] := ⟨c, hc⟩
  have h1 : PadicInt.toZMod (b ^ p - b) = 0 := by rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h2 : b ^ p - b ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact h1
  have h3 : ‖b ^ p - b‖ < 1 := PadicInt.mem_nonunits.1 h2
  obtain ⟨e, he⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h3
  have h4 : ‖c ^ p - c‖ = ‖b ^ p - b‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h4, he, norm_mul, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one e)
end GroundTheory.PAdicHodge
