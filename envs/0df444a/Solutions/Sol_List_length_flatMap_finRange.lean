-- Prove2me | solution 1 for List.length_flatMap_finRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:32.043868+00:00
-- url     : https://prove2.me/submissions/6ecc278d-8ddc-4886-a833-1f2ba0509d99

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k) :
    ((List.finRange n).flatMap f).length = n * k := by
  simp [List.length_flatMap, hf]
end List
