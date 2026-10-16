-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.diagram_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:39:23.281814+00:00
-- url     : https://prove2.me/submissions/7555890b-4566-4d6c-bc34-842021d7a5db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Representation.lean:L9-L79
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.diagram_representation. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_Network_summary_join
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_augmentedStep_local_iff
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_augmented_acceptance
import Theorems.Thm_OAI_TwoWayComplementation_chainStep_recognition
import Theorems.Thm_OAI_TwoWayComplementation_marked_getElem

-- ---- from OAI.Combinatorics.TwoWayAutomata.Network ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem wordDiagram_append {Sigma : Type*} {m : ℕ} (d : Sigma → Diagram m)
    (u v : List Sigma) :
    wordDiagram d (u ++ v) = Diagram.comp (wordDiagram d u) (wordDiagram d v) := by
  change ((u ++ v).map d).prod = (u.map d).prod * (v.map d).prod
  rw [List.map_append, List.prod_append]

namespace Network

end Network

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Chain ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace ChainNode

end ChainNode

/-- The path summary of a cell chain is the product of its cell diagrams. -/
theorem chainNetwork_summary {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    (chainNetwork moves w last).summary =
      wordDiagram (fun a => cellDiagram m (moves a 1) (moves a 2) (moves a 0)) (w ++ [last]) := by
  induction w with
  | nil =>
    change (cellNetwork (moves last)).summary = _
    simp [Network.summary, cellNetwork, cellDiagram, wordDiagram, SetRel.id_comp]
  | cons a w ih =>
    change ((cellNetwork (moves a)).join (chainNetwork moves w last)).summary = _
    rw [Network.summary_join, ih]
    simp only [Network.summary, cellNetwork, SetRel.id_comp, cellDiagram, wordDiagram,
      List.cons_append, List.map_cons, List.prod_cons]
    rfl

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Tape ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Chain symbols agree with ordinary zero-based lookup of the nonempty symbol list. -/
theorem chainSymbol_getElem {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) :
    chainSymbol w last c = (w ++ [last])[c.position]'(by
      have := c.position_le
      simp only [List.length_append, List.length_singleton]
      omega) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases c with
    | inl q => rfl
    | inr c => simpa only [chainSymbol, ChainNode.position, List.cons_append,
        List.getElem_cons_succ] using ih c

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

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Representation ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Every 2NFA has an exact diagram representation with one additional state label. -/
theorem TwoNFA.diagram_representation {Sigma : Type*} {s : ℕ} (A : TwoNFA Sigma (Fin s)) :
    ∃ τ : List Sigma → Diagram (s + 1), ∃ l r : Diagram (s + 1), ∃ a b : Fin (s + 1),
      τ [] = Diagram.identity (s + 1) ∧
      (∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v)) ∧
      (∀ w, w ∈ A.language ↔ (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward) := by
  let e := finSuccEquiv s
  let moves (symbol : Fin 2 ⊕ Sigma) (move : Fin 3) : SetRel (Fin (s + 1)) (Fin (s + 1)) :=
    {qr | (e qr.1, e qr.2) ∈ A.augmentedMove symbol move}
  let d (symbol : Fin 2 ⊕ Sigma) := cellDiagram (s + 1)
    (moves symbol 1) (moves symbol 2) (moves symbol 0)
  let a := e.symm (some A.initial)
  let b := e.symm none
  refine ⟨wordDiagram (fun symbol => d (Sum.inr symbol)), d (Sum.inl 0), d (Sum.inl 1),
    a, b, wordDiagram_nil _, wordDiagram_append _, ?_⟩
  intro w
  let cells : List (Fin 2 ⊕ Sigma) := Sum.inl 0 :: w.map Sum.inr
  let ec : (Fin (s + 1) × Fin (cells.length + 2)) ≃
      (Option (Fin s) × Fin (w.length + 3)) :=
    Equiv.prodCongr e (finCongr (by simp [cells]))
  have hread (c : ChainNode (s + 1) cells.length) (p : Fin (w.length + 2))
      (hp : c.position = p.val) : chainSymbol cells (Sum.inl 1) c = tapeSymbol w p := by
    rw [chainSymbol_getElem]
    simpa only [cells, List.cons_append, hp] using marked_getElem w p
  have hstep (x y : Fin (s + 1) × Fin (cells.length + 2)) :
      (ec x, ec y) ∈ A.augmentedStep w ↔ (x, y) ∈ chainStep moves cells (Sum.inl 1) := by
    rw [A.augmentedStep_local_iff]
    constructor
    · rintro ⟨p, hp, move, hmove, hdisp⟩
      have hpx : p.val = x.2.val := (congrArg Fin.val hp).symm
      have hbound : p.val ≤ cells.length := by simp [cells]; omega
      obtain ⟨c, _, hc⟩ := ChainNode.coordinates_surjective x.1 p.val hbound
      refine ⟨c, hpx.symm.trans hc.symm, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (chainSymbol cells (Sum.inl 1) c) move
        rw [hread c p hc]
        exact hmove
      · change (y.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
        rwa [hpx] at hdisp
    · rintro ⟨c, hpos, move, hmove, hdisp⟩
      have hc : c.position < w.length + 2 := by
        have hbound := c.position_le
        simp only [cells, List.length_cons, List.length_map] at hbound
        omega
      let p : Fin (w.length + 2) := ⟨c.position, hc⟩
      refine ⟨p, Fin.ext hpos, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (tapeSymbol w p) move
        rw [← hread c p rfl]
        exact hmove
      · change (y.2.val : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1
        rwa [hpos] at hdisp
  have hstart : ec (a, ⟨0, by omega⟩) =
      TwoNFA.augmentConfig (A.initial, ⟨0, by omega⟩) :=
    Prod.ext (e.apply_symm_apply _) (Fin.ext rfl)
  have hend : ec (b, ⟨cells.length + 1, by omega⟩) =
      (none, ⟨w.length + 2, by omega⟩) := by
    apply Prod.ext (e.apply_symm_apply _)
    apply Fin.ext
    change cells.length + 1 = w.length + 2
    simp [cells]
  have hpaths := relStar_equiv_iff ec (chainStep moves cells (Sum.inl 1))
    (A.augmentedStep w) hstep (a, ⟨0, by omega⟩) (b, ⟨cells.length + 1, by omega⟩)
  rw [hstart, hend, ← A.augmented_acceptance w] at hpaths
  rw [hpaths, chainStep_recognition, chainNetwork_summary]
  have hprod : wordDiagram d (cells ++ [Sum.inl 1]) =
      Diagram.comp (Diagram.comp (d (Sum.inl 0))
        (wordDiagram (fun symbol => d (Sum.inr symbol)) w)) (d (Sum.inl 1)) := by
    simp only [wordDiagram, cells, List.cons_append, List.map_cons, List.map_append,
      List.prod_cons, List.prod_append, List.map_map, List.map_nil, List.prod_nil, mul_one]
    exact (mul_assoc _ _ _).symm
  change (a, b) ∈ (wordDiagram d (cells ++ [Sum.inl 1])).forward ↔ _
  rw [hprod]

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.diagram_representation := @_root_.OAI.TwoWayComplementation.TwoNFA.diagram_representation
