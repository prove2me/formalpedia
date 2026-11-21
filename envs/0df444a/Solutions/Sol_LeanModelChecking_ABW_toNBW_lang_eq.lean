-- Prove2me | solution 1 for LeanModelChecking.ABW.toNBW.lang_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:46.681354+00:00
-- url     : https://prove2.me/submissions/297d0d2a-0a2b-46a0-b8f1-aaecfeafd815

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_sub
public import Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_sup

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace ABW.toNBW
theorem _root_.solution {S Q} (A : ABW S Q) [Finite Q] : A.language = (ABW.toNBW A).language := by
  funext; apply propext
  exact ⟨ABW.toNBW.lang_sup, ABW.toNBW.lang_sub⟩
end ABW.toNBW
end LeanModelChecking
