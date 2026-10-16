-- Prove2me | solution 1 for OAI.TwoWayComplementation.chainStep_recognition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:37:09.299189+00:00
-- url     : https://prove2.me/submissions/186aefea-7293-4638-b42f-90248f0b39dc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean:L148-L169
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.chainStep_recognition. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape
import Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_cross
import Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_entrances
import Theorems.Thm_OAI_TwoWayComplementation_chainStep_exitEquiv

-- ---- from OAI.Combinatorics.TwoWayAutomata.Tape ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A graph equivalence transports finite paths in both directions. -/
theorem relStar_equiv_iff {V W : Type*} (e : V ≃ W) (R : SetRel V V) (S : SetRel W W)
    (h : ∀ x y, (e x, e y) ∈ S ↔ (x, y) ∈ R) (x y : V) :
    (e x, e y) ∈ relStar S ↔ (x, y) ∈ relStar R := by
  constructor
  · intro hrun
    have hlift := hrun.lift e.symm (p := fun a b => (a, b) ∈ R) (by
      intro a b hab
      apply (h (e.symm a) (e.symm b)).mp
      simpa only [Equiv.apply_symm_apply] using hab)
    change Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hlift
  · exact fun hrun => hrun.lift e (fun a b hab => (h a b).mpr hab)

/-- A terminal block with no outgoing edges is reached by an internal path and one exit. -/
theorem blockRelation_terminal {V Q : Type*} (E : SetRel V V) (O : SetRel V Q)
    (c : V) (q : Q) :
    (Sum.inl c, Sum.inr q) ∈ relStar (blockRelation E O ∅ ∅) ↔
      (c, q) ∈ relStar E ○ O := by
  rw [blockRelation_star_cross]
  simp only [SetRel.empty_comp, Set.empty_union, relStar_empty, SetRel.comp_id]

/-- The designated forward edge of a diagram product is exactly a successful tape run. -/
theorem chainStep_recognition {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q r : Fin m) :
    ((q, ⟨0, by omega⟩), (r, ⟨w.length + 1, by omega⟩)) ∈ relStar (chainStep moves w last) ↔
      (q, r) ∈ (chainNetwork moves w last).summary.forward := by
  obtain ⟨c, hq, hp⟩ := ChainNode.coordinates_surjective (n := w.length) q 0 (Nat.zero_le _)
  have hstart : ChainNode.exitEquiv m w.length (Sum.inl c) = (q, ⟨0, by omega⟩) :=
    Prod.ext hq (Fin.ext hp)
  have hend : ChainNode.exitEquiv m w.length (Sum.inr r) =
      (r, ⟨w.length + 1, by omega⟩) := rfl
  rw [← hstart, ← hend, relStar_equiv_iff (ChainNode.exitEquiv m w.length)
    (blockRelation (chainNetwork moves w last).edge (chainNetwork moves w last).rightOut ∅ ∅)
    (chainStep moves w last) (chainStep_exitEquiv moves w last), blockRelation_terminal]
  constructor
  · rintro ⟨d, hcd, hdr⟩
    exact ⟨d, ⟨c, (chainNetwork_entrances moves w last q c).1.mpr ⟨hp, hq.symm⟩,
      hcd⟩, hdr⟩
  · rintro ⟨d, ⟨c', hqc, hcd⟩, hdr⟩
    obtain ⟨hp', hq'⟩ := (chainNetwork_entrances moves w last q c').1.mp hqc
    have hc : c' = c := c'.coordinates_injective c (hp'.trans hp.symm) (hq'.symm.trans hq.symm)
    exact ⟨d, hc ▸ hcd, hdr⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.chainStep_recognition := @_root_.OAI.TwoWayComplementation.chainStep_recognition
