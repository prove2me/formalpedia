-- Prove2me | solution 1 for IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/61eb0683-e8c1-5f3f-8c0f-c6c5df63569e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne

set_option autoImplicit false

open Set Order TopologicalSpace Topology

universe u

namespace P2mDim

variable {X : Type u} [TopologicalSpace X] {Y Z : Set X}

def topIC (hZ : IsIrreducible Z) : IrreducibleCloseds Z where
  carrier := univ
  isIrreducible' := by
    haveI : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    exact IrreducibleSpace.isIrreducible_univ Z
  isClosed' := isClosed_univ

def push (hYZ : Y ⊆ Z) : IrreducibleCloseds Y → IrreducibleCloseds Z :=
  IrreducibleCloseds.map (inclusion hYZ) (continuous_inclusion hYZ)

theorem push_strictMono (hYZ : Y ⊆ Z) : StrictMono (push (X := X) hYZ) :=
  IrreducibleCloseds.map_strictMono_of_isInducing (IsEmbedding.inclusion hYZ).isInducing

theorem coe_push_subset (hYZ : Y ⊆ Z) (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    ((push hYZ s : IrreducibleCloseds Z) : Set Z) ⊆ (Subtype.val ⁻¹' Y : Set Z) := by
  show closure (inclusion hYZ '' (s : Set Y)) ⊆ _
  refine closure_minimal ?_ (hY.preimage continuous_subtype_val)
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem push_lt_top (hZ : IsIrreducible Z) (hYZ : Y ⊆ Z) (hY : IsClosed Y) (hne : Y ≠ Z)
    (s : IrreducibleCloseds Y) : push hYZ s < topIC hZ := by
  refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
  refine subset_antisymm hYZ fun z hz => ?_
  have hmem : (⟨z, hz⟩ : Z) ∈ ((push hYZ s : IrreducibleCloseds Z) : Set Z) := by
    rw [h]; trivial
  exact coe_push_subset hYZ hY s hmem

theorem main (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by
  unfold topologicalKrullDim
  cases isEmpty_or_nonempty (IrreducibleCloseds Y) with
  | inl h =>
    rw [krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [← krullDim_WithTop]

    let g : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds Z :=
      fun a => WithTop.recTopCoe (topIC hZ) (fun s => push hYZ s) a
    refine krullDim_le_of_strictMono g fun a b hab => ?_
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe s =>
      induction b using WithTop.recTopCoe with
      | top => exact push_lt_top hZ hYZ hY hne s
      | coe t => exact push_strictMono hYZ (WithTop.coe_lt_coe.mp hab)

end P2mDim

theorem solution
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z :=
  P2mDim.main hZ hY hYZ hne

end S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
end P2MW
export P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne (solution)
