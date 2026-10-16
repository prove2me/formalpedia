-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:05:42.760796+00:00
-- url     : https://prove2.me/submissions/5e53903b-4887-49dd-b9c7-659b25495014

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Main.lean:L60-L82
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main

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

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Main ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Letter maps commute with tape lookup and preserve the two endmarkers. -/
theorem tapeSymbol_map {Sigma Gamma : Type*} (f : Sigma → Gamma) (w : List Sigma)
    (p : Fin (w.length + 2)) :
    tapeSymbol (w.map f) ⟨p.val, by simp⟩ =
      Sum.map id f (tapeSymbol w p) := by
  simp only [tapeSymbol, List.length_map, List.getElem_map]
  split_ifs <;> rfl

/-- Letter pullback accepts exactly the words whose images the original machine accepts. -/
theorem TwoNFA.pullAlphabet_language {Sigma Gamma Q : Type*} (A : TwoNFA Gamma Q)
    (f : Sigma → Gamma) (w : List Sigma) :
    w ∈ (A.pullAlphabet f).language ↔ w.map f ∈ A.language := by
  let e : (Q × Fin (w.length + 2)) ≃ (Q × Fin ((w.map f).length + 2)) :=
    Equiv.prodCongr (Equiv.refl Q) (finCongr (by simp))
  have hstep (c d : Q × Fin (w.length + 2)) :
      (e c, e d) ∈ A.step (w.map f) ↔ (c, d) ∈ (A.pullAlphabet f).step w := by
    change (∃ move : Fin 3,
      (d.1, move) ∈ A.transition c.1
        (tapeSymbol (w.map f) ⟨c.2.val, by simp⟩) ∧
      (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1) ↔ _
    rw [tapeSymbol_map]
    rfl
  constructor
  · rintro ⟨c, hc, hrun⟩
    refine ⟨e c, hc, ?_⟩
    exact (relStar_equiv_iff e _ _ hstep (A.initial, ⟨0, by omega⟩) c).mpr hrun
  · rintro ⟨d, hd, hrun⟩
    refine ⟨e.symm d, hd, ?_⟩
    apply (relStar_equiv_iff e _ _ hstep (A.initial, ⟨0, by omega⟩) (e.symm d)).mp
    rw [Equiv.apply_symm_apply]
    exact hrun

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language := @_root_.OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language
