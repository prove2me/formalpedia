-- Prove2me | solution 1 for OAI.TwoWayComplementation.diagram_relation_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:23:53.077431+00:00
-- url     : https://prove2.me/submissions/62a29e2b-8178-4fd5-94b4-4db2a6914dc8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean:L36-L88
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.diagram_relation_image. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_word_diagram_order_reversal

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem inclusion_refl {m : ℕ} (a : Diagram m) : (a, a) ∈ inclusion m :=
  ⟨Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Source ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem relationProduct_append {H : Type*} (u v : List (SetRel H H)) :
    relationProduct (u ++ v) = relationProduct u ○ relationProduct v := by
  induction u with
  | nil => simp [relationProduct]
  | cons R u ih => simpa [relationProduct, SetRel.comp_assoc] using congrArg (R ○ ·) ih

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Recognition ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The relation product descends to the diagram image by singleton-context tests. -/
theorem diagram_relation_image {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) :
    ∃ S : Submonoid (Diagram m), ∃ φ : S →* RelationMonoid H,
      Function.Surjective φ ∧
      (∀ z w : S, (z.val, w.val) ∈ Diagram.inclusion m → (φ w).toRel ⊆ (φ z).toRel) := by
  classical
  let S : Submonoid (Diagram m) :=
    { carrier := Set.range τ
      one_mem' := ⟨[], hzero⟩
      mul_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u ++ v, hmul u v⟩ }
  have hword (z : S) : ∃ w, τ w = z.val := z.property
  choose word hwordeq using hword
  have hwell {u v : List (SetRel H H)} (huv : τ u = τ v) :
      relationProduct u = relationProduct v := by
    apply Set.Subset.antisymm
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
  have hvalue (z : S) (w : List (SetRel H H)) (hw : τ w = z.val) :
      relationProduct (word z) = relationProduct w := hwell ((hwordeq z).trans hw.symm)
  let φ : S →* RelationMonoid H :=
    { toFun := fun z => .ofRel (relationProduct (word z))
      map_one' := by
        apply RelationMonoid.ext
        exact hvalue 1 [] hzero
      map_mul' := by
        intro z w
        apply RelationMonoid.ext
        change relationProduct (word (z * w)) = relationProduct (word z) ○ relationProduct (word w)
        rw [hvalue (z * w) (word z ++ word w) (by rw [hmul, hwordeq, hwordeq]; rfl)]
        exact relationProduct_append _ _ }
  refine ⟨S, φ, ?_, ?_⟩
  · intro R
    refine ⟨⟨τ [R.toRel], [R.toRel], rfl⟩, ?_⟩
    apply RelationMonoid.ext
    change relationProduct (word _) = R.toRel
    rw [hvalue _ [R.toRel] rfl]
    simp [relationProduct]
  · intro z w hzw
    change relationProduct (word w) ⊆ relationProduct (word z)
    apply word_diagram_order_reversal τ hmul l r a b hlanguage
    rwa [hwordeq, hwordeq]

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.diagram_relation_image := @_root_.OAI.TwoWayComplementation.diagram_relation_image
