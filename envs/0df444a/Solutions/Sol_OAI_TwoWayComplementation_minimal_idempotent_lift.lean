-- Prove2me | solution 1 for OAI.TwoWayComplementation.minimal_idempotent_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:46:31.747426+00:00
-- url     : https://prove2.me/submissions/cec9ea95-59cc-4f1c-b1de-c1d15f5a8db4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean:L99-L124
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.minimal_idempotent_lift. The node keeps its source
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

/-- An idempotent has a lift minimal in the nesting order. -/
theorem minimal_idempotent_lift {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) (q : M) (hq : IsIdempotentElem q) :
    ∃ d, IsIdempotentElem d ∧ θ d = q ∧
      ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d := by
  obtain ⟨a, ha⟩ := hθ q
  obtain ⟨d0, hd0q, hd0⟩ := finite_subsemigroup_idempotent
    {x | θ x = q} ⟨a, ha⟩ (by
      intro x hx y hy
      change θ (x * y) = q
      rw [map_mul, hx, hy, hq.eq])
  obtain ⟨d, ⟨hd, hdq⟩, hminimal⟩ := Set.exists_min_image
    {d | IsIdempotentElem d ∧ θ d = q}
    (fun d => (Subsemigroup.corner d : Set A).ncard) (Set.toFinite _) ⟨d0, hd0, hd0q⟩
  refine ⟨d, hd, hdq, ?_⟩
  intro e he heq hed hde
  have hsub : (Subsemigroup.corner e : Set A) ⊆ Subsemigroup.corner d := by
    rintro x ⟨y, rfl⟩
    apply (Subsemigroup.mem_corner_iff hd).mpr
    exact ⟨by simp only [← mul_assoc, hde], by simp only [mul_assoc, hed]⟩
  have heqcorner := Set.eq_of_subset_of_ncard_le hsub (hminimal e ⟨he, heq⟩)
  have hdin : d ∈ Subsemigroup.corner e := by
    change d ∈ (Subsemigroup.corner e : Set A)
    rw [heqcorner]
    exact (Subsemigroup.mem_corner_iff hd).mpr ⟨hd, hd⟩
  exact hed.symm.trans ((Subsemigroup.mem_corner_iff he).mp hdin).1

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.minimal_idempotent_lift := @_root_.OAI.TwoWayComplementation.minimal_idempotent_lift
