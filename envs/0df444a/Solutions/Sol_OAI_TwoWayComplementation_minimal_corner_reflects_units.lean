-- Prove2me | solution 1 for OAI.TwoWayComplementation.minimal_corner_reflects_units
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:48:22.871103+00:00
-- url     : https://prove2.me/submissions/77af81df-f280-43e1-ab37-deb317496cbf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean:L161-L178
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.minimal_corner_reflects_units. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners

-- ---- from OAI.Combinatorics.TwoWayAutomata.Corners ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A finite nonempty subsemigroup contains an idempotent. -/
theorem finite_subsemigroup_idempotent {A : Type*} [Semigroup A] [Finite A]
    (S : Set A) (hne : S.Nonempty) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) :
    ∃ e ∈ S, IsIdempotentElem e := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact exists_idempotent_in_compact_subsemigroup (fun _ => continuous_of_discreteTopology)
    S hne (Set.toFinite S).isCompact hmul

/-- Every element of a finite monoid has an idempotent positive power. -/
theorem finite_idempotent_pow {A : Type*} [Monoid A] [Finite A] (a : A) :
    ∃ k : ℕ, 0 < k ∧ IsIdempotentElem (a ^ k) := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := finite_subsemigroup_idempotent
    (Set.range (fun k : ℕ => a ^ (k + 1))) ⟨a, 0, by simp⟩ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨i + j + 1, by simp only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩)
  exact ⟨k + 1, Nat.succ_pos _, hk⟩

/-- At a minimal idempotent lift, every element with unit image is a unit. -/
theorem minimal_corner_reflects_units {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q)
    (hθd : θ d = q)
    (hminimal : ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d)
    (w : hd.Corner) (hw : IsUnit (cornerMap θ hd hq hθd w)) : IsUnit w := by
  obtain ⟨k, hk, hpow⟩ := finite_idempotent_pow w
  have hmapIdem : IsIdempotentElem (cornerMap θ hd hq hθd (w ^ k)) := by
    change _ * _ = _
    rw [← map_mul, hpow.eq]
  have hmapUnit : IsUnit (cornerMap θ hd hq hθd (w ^ k)) := by
    rw [map_pow]
    exact hw.pow k
  have hmapOne := (IsIdempotentElem.iff_eq_one_of_isUnit hmapUnit).mp hmapIdem
  have hθpow : θ (w ^ k).val = q := congrArg Subtype.val hmapOne
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hd).mp (w ^ k).property
  have hwd : (w ^ k).val = d := hminimal _ (congrArg Subtype.val hpow.eq) hθpow hr hl
  exact IsUnit.of_pow_eq_one (Subtype.ext hwd) hk.ne'

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.minimal_corner_reflects_units := @_root_.OAI.TwoWayComplementation.minimal_corner_reflects_units
