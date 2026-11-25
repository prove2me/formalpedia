-- Prove2me | solution 1 for MonotoneLight.surjective_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:47.847442+00:00
-- url     : https://prove2.me/submissions/de6c8ce9-4ca9-4aee-b4ae-9ecdf0a3626e

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
theorem _root_.solution {f : X → Y} (hf : Surjective f) : Surjective (light f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨monotone f x, rfl⟩
end MonotoneLight
