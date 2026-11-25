-- Prove2me | solution 1 for MonotoneLight.light_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:45.573745+00:00
-- url     : https://prove2.me/submissions/fe89682b-4846-46f8-b43d-06a3522313c4

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
theorem _root_.solution (f : X → Y) (x : X) :
    light f (monotone f x) = f x := rfl
end MonotoneLight
