-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:36.784315+00:00
-- url     : https://prove2.me/submissions/e882781f-724e-427d-844b-801ee878e33d

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
theorem _root_.solution (a : W) : RIn G s a a := Relation.ReflTransGen.refl
end LeanPool.K5MinorFreeChoosability.RIn
