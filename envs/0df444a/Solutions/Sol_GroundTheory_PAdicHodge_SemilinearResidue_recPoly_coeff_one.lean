-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:11.185315+00:00
-- url     : https://prove2.me/submissions/a1848077-ab0c-4d1e-a5ee-b07bf819e5de

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_coeff_pow_prime_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow

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
variable {e : ℕ}
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ i, (recPoly (p ^ e) c ε i).coeff 1 = 0 := by
  have h2 := two_le_pow (p := p) he
  have hq1 : (1 : ℕ) ≠ p ^ e := by omega
  have hnd : ¬ p ^ e ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  intro i
  cases i with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, hq1]
  | succ i => simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, hnd]
end GroundTheory.PAdicHodge.SemilinearResidue
