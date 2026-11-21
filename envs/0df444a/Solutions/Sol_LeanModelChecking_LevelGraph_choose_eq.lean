-- Prove2me | solution 1 for LeanModelChecking.LevelGraph.choose_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:08.698323+00:00
-- url     : https://prove2.me/submissions/b3104f32-444f-487d-92e7-869b62b8e5c1

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LevelGraph
namespace LeanModelChecking.LevelGraph
theorem _root_.solution {α} {p : α → Prop} (P : ∃ a, p a) {a} (eq : P.choose = a) : p a :=
  eq ▸ P.choose_spec
end LeanModelChecking.LevelGraph
