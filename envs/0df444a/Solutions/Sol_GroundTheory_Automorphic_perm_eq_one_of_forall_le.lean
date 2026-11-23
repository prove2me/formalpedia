-- Prove2me | solution 1 for GroundTheory.Automorphic.perm_eq_one_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:59.436273+00:00
-- url     : https://prove2.me/submissions/e9895dcb-0d4b-4f3e-9dfa-cc98fb55509c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (π : Equiv.Perm (Fin n)) (h : ∀ x, π x ≤ x) : π = 1 := by
  have hsum : ∑ x, ((π x : Fin n) : ℕ) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp π (fun x : Fin n => (x : ℕ))
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun x _ => Fin.le_iff_val_le_val.mp (h x))).mp hsum
  exact Equiv.ext fun x => by simpa using Fin.ext (heq x (Finset.mem_univ _))
end GroundTheory.Automorphic
