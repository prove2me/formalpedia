-- Prove2me | solution 1 for NagataFactoriality.listProd_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:28.115992+00:00
-- url     : https://prove2.me/submissions/41958191-fd17-47fa-a18c-e15d17c54469

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_NagataFactoriality_listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] (xs ys : List α) :
    listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih => simp [listProd, ih, mul_assoc]
end NagataFactoriality
