-- Prove2me | solution 1 for MonotoneLight.monotone_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:23.889549+00:00
-- url     : https://prove2.me/submissions/324a86b3-2d5b-4d3d-ab87-54a63a6cc349

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
omit [TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution {f : X → Y} {x y : X} :
    monotone f x = monotone f y ↔ FiberRel f x y := Quotient.eq
end MonotoneLight
