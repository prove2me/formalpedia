-- Prove2me | solution 1 for LeanModelChecking.PositiveBool.Sat.monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:44.665565+00:00
-- url     : https://prove2.me/submissions/0ee0ae87-77dc-4c97-94e7-46123df13df7

module
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_LeanModelChecking_ABW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace PositiveBool.Sat
theorem _root_.solution {Q} {f : PositiveBool Q} {A B : Set Q} :
    A ⊆ B → PositiveBool.Sat A f → PositiveBool.Sat B f := by
  induction f <;> grind [Sat]
end PositiveBool.Sat
end LeanModelChecking
