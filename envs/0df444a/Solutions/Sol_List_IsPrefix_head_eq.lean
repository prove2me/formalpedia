-- Prove2me | solution 1 for List.IsPrefix.head_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:48.883367+00:00
-- url     : https://prove2.me/submissions/79509356-3ab7-4b93-b482-ea6d591d5572

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Widget.Calc
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open List
namespace List
namespace IsPrefix
theorem _root_.solution {α : Type*} {s t : List α} (h : s <+: t) (hne : s ≠ []) :
    t.head? = s.head? := by
  obtain ⟨u, rfl⟩ := h
  cases s with
  | nil => exact absurd rfl hne
  | cons a s' => simp
end IsPrefix
end List
