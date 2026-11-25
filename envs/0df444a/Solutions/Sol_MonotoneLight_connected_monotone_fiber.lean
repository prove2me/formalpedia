-- Prove2me | solution 1 for MonotoneLight.connected_monotone_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:19.495208+00:00
-- url     : https://prove2.me/submissions/47e718c5-5ef6-4030-975a-7d5c1906d748

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_monotone_eq_iff
public import Theorems.Thm_MonotoneLight_surjective_monotone
public import Theorems.Thm_MonotoneLight_light_monotone
attribute [local simp] MonotoneLight.light_monotone

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
omit [TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution (f : X → Y) (z : Middle f) :
    IsConnected (monotone f ⁻¹' {z}) := by
  obtain ⟨x, rfl⟩ := surjective_monotone f z
  have he : monotone f ⁻¹' {monotone f x} = connectedComponentIn (f ⁻¹' {f x}) x := by
    ext y
    exact monotone_eq_iff.trans ⟨(fiberSetoid f).symm, (fiberSetoid f).symm⟩
  rw [he]
  exact isConnected_connectedComponentIn_iff.mpr rfl
end MonotoneLight
