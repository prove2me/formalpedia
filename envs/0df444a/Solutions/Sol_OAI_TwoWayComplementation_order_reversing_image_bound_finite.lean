-- Prove2me | solution 1 for OAI.TwoWayComplementation.order_reversing_image_bound_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:13:32.154613+00:00
-- url     : https://prove2.me/submissions/7acf8ff0-17e3-4914-b659-4fb107f0bfc2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean:L221-L268
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.order_reversing_image_bound_finite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Theorems.Thm_OAI_TwoWayComplementation_minimal_idempotent_lift
import Theorems.Thm_OAI_TwoWayComplementation_minimal_unital_corner
import Theorems.Thm_OAI_TwoWayComplementation_single_edge_cost

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

/-- There are at most two signed recurrent classes per boundary label. -/
theorem class_count {m : ℕ} (e : Diagram m) : e.classes.ncard ≤ 2 * m := by
  let f : Bool × Fin m → Bool × Set (Fin m) := fun p =>
    (p.1, {y | (p.2, y) ∈ e.recurrence p.1 ∧ (y, p.2) ∈ e.recurrence p.1})
  have hsub : e.classes ⊆ f '' Set.univ := by
    rintro ⟨positive, C⟩ ⟨x, _, hC⟩
    exact ⟨(positive, x), Set.mem_univ _, Prod.ext rfl hC.symm⟩
  calc
    e.classes.ncard ≤ (f '' Set.univ).ncard := Set.ncard_le_ncard hsub
    _ ≤ (Set.univ : Set (Bool × Fin m)).ncard := Set.ncard_image_le
    _ = 2 * m := by simp

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ImageBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TwoWayComplementation

universe u v

open scoped SetRel

/-- Identity plus a single pair is always an idempotent relation. -/
theorem identity_pair_idempotent {H : Type*} (x y : H) :
    IsIdempotentElem (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) := by
  apply RelationMonoid.ext
  change (SetRel.id ∪ {(x, y)}) ○ (SetRel.id ∪ {(x, y)}) = SetRel.id ∪ {(x, y)}
  ext ⟨r, s⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, Prod.mk.injEq]
  aesop

/-- A surjective order-reversing multiplicative image has exponential cost. -/
theorem order_reversing_image_bound_finite {H : Type*} [Finite H]
    (m : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ Nat.card H)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel H H) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound (Nat.card H) ≤ 2 * m := by
  classical
  let S0 : Submonoid (Diagram m) :=
    { carrier := S
      one_mem' := hidentity
      mul_mem' := by
        intro a b ha hb
        change Diagram.comp a b ∈ S
        exact hclosed ha hb }
  let θ : S0 →ₙ* RelationMonoid H :=
    { toFun := fun x => .ofRel (φ ⟨x.val, x.property⟩)
      map_mul' := fun a b => RelationMonoid.ext (hmul ⟨a.val, a.property⟩ ⟨b.val, b.property⟩) }
  have hθ : Function.Surjective θ := by
    intro R
    obtain ⟨x, hx⟩ := hsurj R.toRel
    exact ⟨⟨x.val, x.property⟩, RelationMonoid.ext hx⟩
  obtain ⟨e, he, ψ, hψ, hψval, hunit⟩ := minimal_unital_corner θ hθ
  let ι : he.Corner →ₙ* Diagram m :=
    { toFun := fun w => w.val.val
      map_mul' := fun _ _ => rfl }
  have hrev : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (ψ b).toRel ⊆ (ψ a).toRel := by
    intro a b hab
    rw [hψval, hψval]
    exact hreverse ⟨a.val.val, a.val.property⟩ ⟨b.val.val, b.val.property⟩ hab
  let := Fintype.ofFinite H
  obtain ⟨pair⟩ : Nonempty (Fin 2 ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let x := pair 0
  let y := pair 1
  have hxy : x ≠ y := fun heq => by
    have := congrArg Fin.val (pair.injective heq)
    norm_num at this
  obtain ⟨a, ha, haimage, _⟩ := minimal_idempotent_lift ψ.toMulHom hψ
    (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) (identity_pair_idempotent x y)
  have hcost := single_edge_cost (Nat.card H) rfl hh ι ψ hψ hrev
    (fun σ => hunit (permutationUnit σ)) a ha x y hxy
    (congrArg RelationMonoid.toRel haimage)
  exact hcost.trans ((Set.ncard_le_ncard (show (ι 1).missing (ι a) ⊆ (ι 1).classes from
    fun _ h => h.1)).trans (Diagram.class_count (ι 1)))

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.order_reversing_image_bound_finite := @_root_.OAI.TwoWayComplementation.order_reversing_image_bound_finite
