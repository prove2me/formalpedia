-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.levelHom_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:16.69345+00:00
-- url     : https://prove2.me/submissions/5bc00bb6-91a2-419a-a677-7937f7fadc90

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_apply

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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = 1 ↔ (u : ℤ_[p]ˣ) ∈ unitsOneAdd p (k + 1) := by
  rw [levelHom_apply, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, mem_unitsOneAdd, levelQuot_spec,
    pow_succ]
  have hp0 : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact (mul_dvd_mul_iff_left hp0).symm
end GroundTheory.PAdicHodge.SenTateChar
