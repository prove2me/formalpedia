-- Prove2me | solution 1 for MonotoneLight.surjective_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:29.276644+00:00
-- url     : https://prove2.me/submissions/b7cb59ea-3a1a-4688-bbfc-da88de2a8d4d

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
theorem _root_.solution (f : X → Y) : Surjective (monotone f) :=
  Quotient.mk_surjective
end MonotoneLight
