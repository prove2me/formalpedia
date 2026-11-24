-- Prove2me | solution 1 for Mader.dbl_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:04.094366+00:00
-- url     : https://prove2.me/submissions/bfcd33d2-219b-46ff-953c-f25509a23ceb

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Theorems.Thm_Mader_dbl_eq_sum
public import Theorems.Thm_Mader_ndeg_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
namespace Mader
theorem _root_.solution (S : Finset V) : dbl G S ≤ S.card * (S.card - 1) := by
  classical
  rw [dbl_eq_sum]
  calc _ ≤ ∑ _v ∈ S, (S.card - 1) := sum_le_sum (fun v hv => ndeg_le G hv)
    _ = _ := by simp
end Mader
