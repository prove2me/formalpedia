-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.coeff_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:49.692798+00:00
-- url     : https://prove2.me/submissions/2c0779fe-2abe-4710-ae66-998504ef81d8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue

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
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
include hp
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution (f : k[X]) (e n : ℕ) :
    (f ^ p ^ e).coeff n = if p ^ e ∣ n then f.coeff (n / p ^ e) ^ p ^ e else 0 := by
  have : ExpChar k p := ExpChar.prime hp.out
  rw [← map_iterateFrobenius_expand p f e, coeff_map, coeff_expand (pow_pos hp.out.pos e)]
  split_ifs <;> simp [iterateFrobenius_def, hp.out.ne_zero]
end GroundTheory.PAdicHodge.SemilinearResidue
