-- Prove2me | solution 1 for OAI.TwoWayComplementation.diagram_recognition_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:25:16.388702+00:00
-- url     : https://prove2.me/submissions/6f1023cc-f1fd-4e12-b6ef-c66e6c5b7a4f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean:L90-L110
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.diagram_recognition_lower_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source
import Theorems.Thm_OAI_TwoWayComplementation_diagram_relation_image
import Theorems.Thm_OAI_TwoWayComplementation_order_reversing_image_bound_finite

-- ---- from OAI.Combinatorics.TwoWayAutomata.ImageBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TwoWayComplementation

universe u v

open scoped SetRel

/-- The order-reversing image bound for a finite label domain. -/
theorem order_reversing_image_bound
    (m h : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ h)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel (Fin h) (Fin h)) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound h ≤ 2 * m := by
  simpa only [Nat.card_fin] using order_reversing_image_bound_finite (H := Fin h) m _hm
    (by simpa using hh) S hidentity hclosed φ hsurj hmul hreverse

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Recognition ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Recognition of relation-product emptiness forces the image theorem's state bound. -/
theorem diagram_recognition_lower_bound (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (τ : List (SetRel (Fin h) (Fin h)) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) : lossBound h ≤ 2 * m := by
  obtain ⟨S, φ, hsurj, hreverse⟩ := diagram_relation_image τ hzero hmul l r a b hlanguage
  apply order_reversing_image_bound m h hm hh S S.one_mem (by
    intro z w hz hw
    change z * w ∈ S
    exact S.mul_mem hz hw)
    (fun z => (φ z).toRel)
  · intro R
    obtain ⟨z, hz⟩ := hsurj (RelationMonoid.ofRel R)
    exact ⟨z, congrArg RelationMonoid.toRel hz⟩
  · intro z w
    change (φ (z * w)).toRel = (φ z).toRel ○ (φ w).toRel
    rw [map_mul, RelationMonoid.toRel_mul]
  · exact hreverse

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.diagram_recognition_lower_bound := @_root_.OAI.TwoWayComplementation.diagram_recognition_lower_bound
