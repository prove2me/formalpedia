-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.edgeKey_lt_of_precedes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:21:36.941808+00:00
-- url     : https://prove2.me/submissions/00db4c98-48ac-4706-bc36-3ea666d30894

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_lowEnd_lt

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution {u' v' : ℕ} (hu : u < n) (hv : v < n) (hu' : u' < n)
    (hv' : v' < n) (h : Precedes n u v u' v') : edgeKey n u v < edgeKey n u' v' := by
  have h1 := lowEnd_lt (n := n) hu hv
  have h2 := lowEnd_lt (n := n) hu' hv'
  unfold edgeKey
  rcases h with h | ⟨h, h'⟩
  · have : diagIndex n u v / 2 * n + n ≤ diagIndex n u' v' / 2 * n := by
      have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
      simpa [Nat.succ_mul] using this
    omega
  · rw [h]
    omega
end LeanPool.ListEdgeColoringComplete
