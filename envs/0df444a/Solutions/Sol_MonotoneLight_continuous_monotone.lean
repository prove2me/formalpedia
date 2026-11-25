-- Prove2me | solution 1 for MonotoneLight.continuous_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:58.541354+00:00
-- url     : https://prove2.me/submissions/b80aafca-96f2-4edd-8372-4591865c0d77

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
theorem _root_.solution (f : X → Y) : Continuous (monotone f) :=
  continuous_quotient_mk'
end MonotoneLight
