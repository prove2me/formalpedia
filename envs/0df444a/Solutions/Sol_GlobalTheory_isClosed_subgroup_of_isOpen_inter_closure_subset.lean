-- Prove2me | solution 1 for GlobalTheory.isClosed_subgroup_of_isOpen_inter_closure_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:34.015801+00:00
-- url     : https://prove2.me/submissions/21d02b61-ccca-4a58-b92e-1658d89616bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [ContinuousInv G]
namespace GlobalTheory
theorem _root_.solution (H : Subgroup G) {V : Set G}
    (hV : IsOpen V) (hVH : V ∩ closure (H : Set G) ⊆ H) (hne : (V ∩ closure (H : Set G)).Nonempty) :
    IsClosed (H : Set G) := by
  obtain ⟨u, huV, huK⟩ := hne
  have huH : u ∈ H := hVH ⟨huV, huK⟩
  have hmul : ∀ g ∈ closure (H : Set G), ∀ h ∈ H, g * h ∈ closure (H : Set G) := fun g hg h hh =>
    map_mem_closure (f := fun x => x * h) (continuous_mul_const h) hg fun x hx => H.mul_mem hx hh
  refine isClosed_of_closure_subset fun g hg => ?_
  have hg' : g⁻¹ ∈ closure (H : Set G) :=
    map_mem_closure continuous_inv hg fun x hx => H.inv_mem hx
  obtain ⟨h, hhV, hhH⟩ := mem_closure_iff.1 (hmul _ hg' u huH) ((fun y => g * y) ⁻¹' V)
    (hV.preimage (continuous_const_mul g)) (by simpa using huV)
  have : g * h ∈ H := hVH ⟨hhV, hmul g hg h hhH⟩
  simpa using H.mul_mem this (H.inv_mem hhH)
end GlobalTheory
