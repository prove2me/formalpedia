-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:47.949803+00:00
-- url     : https://prove2.me/submissions/aec09f89-833b-4cd1-8a87-a762673dfee1

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h₁ : RIn G s a b) (h₂ : RIn G s b c) : RIn G s a c :=
  Relation.ReflTransGen.trans h₁ h₂
end LeanPool.K5MinorFreeChoosability.RIn
