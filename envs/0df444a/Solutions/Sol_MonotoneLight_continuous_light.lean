-- Prove2me | solution 1 for MonotoneLight.continuous_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:40.239384+00:00
-- url     : https://prove2.me/submissions/1bc5880a-764e-4272-8e1e-09576600419d

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
namespace MonotoneLight
theorem _root_.solution {f : X → Y} (hf : Continuous f) : Continuous (light f) :=
  hf.quotient_lift _
end MonotoneLight
