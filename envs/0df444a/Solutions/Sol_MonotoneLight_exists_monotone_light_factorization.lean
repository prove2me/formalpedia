-- Prove2me | solution 1 for MonotoneLight.exists_monotone_light_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:00:07.373448+00:00
-- url     : https://prove2.me/submissions/495a9373-4d30-4699-9a22-2c2378026709

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_monotone_eq_iff
public import Theorems.Thm_MonotoneLight_continuous_monotone
public import Theorems.Thm_MonotoneLight_surjective_monotone
public import Theorems.Thm_MonotoneLight_middle_t2Space
public import Theorems.Thm_MonotoneLight_continuous_light
public import Theorems.Thm_MonotoneLight_surjective_light
public import Theorems.Thm_MonotoneLight_connected_monotone_fiber
public import Theorems.Thm_MonotoneLight_totallyDisconnected_light_fiber

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X]
    [_cY : CompactSpace Y] [_hY : T2Space Y] {f : X → Y} (hf : Continuous f) (hs : Surjective f) :
    ∃ (Z : Type u) (tZ : TopologicalSpace Z), letI := tZ;
      CompactSpace Z ∧ T2Space Z ∧ ∃ (m : X → Z) (l : Z → Y),
        Continuous m ∧ Surjective m ∧ Continuous l ∧ Surjective l ∧
        f = l ∘ m ∧ (∀ z, IsConnected (m ⁻¹' {z})) ∧
        (∀ y, IsTotallyDisconnected (l ⁻¹' {y})) ∧
        (∀ x y, m x = m y ↔ FiberRel f x y) := by
  refine ⟨Middle f, inferInstance, ?_, middle_t2Space hf, monotone f, light f,
    continuous_monotone f, surjective_monotone f, continuous_light hf,
    surjective_light hs, rfl, connected_monotone_fiber f,
    totallyDisconnected_light_fiber hf, fun _ _ => monotone_eq_iff⟩
  exact Quotient.compactSpace
end MonotoneLight
