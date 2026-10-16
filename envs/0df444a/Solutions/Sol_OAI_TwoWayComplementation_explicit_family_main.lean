-- Prove2me | solution 1 for OAI.TwoWayComplementation.explicit_family_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:17:57.750331+00:00
-- url     : https://prove2.me/submissions/93f4588a-1734-436b-a1ed-1526018629de

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/ExplicitFamily.lean:L35-L50
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TwoWayComplementation.explicit_family_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TwoWayComplementation_explicit_family_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge
import Theorems.Thm_OAI_TwoWayComplementation_CompanionBridge_toDMachine_accepts
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_pullAlphabet_language
import Theorems.Thm_OAI_TwoWayComplementation_deterministic_rate
import Theorems.Thm_OAI_TwoWayComplementation_explicit_complementation_family
import Theorems.Thm_OAI_OneWayLiveness_PathNFA_accepts_iff
import Theorems.Thm_OAI_OneWayLiveness_deterministic_lower_bound

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace TwoNFA

theorem reindex_language {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') :
    (A.reindex e).language = A.language := by
  ext w
  constructor
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e.symm q, p), haccept, ?_⟩
    have h := hrun.lift (fun c : Q' × Fin (w.length + 2) => (e.symm c.1, c.2))
      (p := fun c d => (c, d) ∈ A.step w) (fun _ _ h => h)
    simpa only [Function.onFun, reindex, relStar, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using h
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e q, p), ?_, ?_⟩
    · simpa only [reindex, Set.mem_preimage, Equiv.symm_apply_apply] using haccept
    · exact hrun.lift (fun c : Q × Fin (w.length + 2) => (e c.1, c.2))
        (fun c d h => by
          simpa only [Function.onFun, step, reindex, Set.mem_ofPred_eq,
            Equiv.symm_apply_apply] using h)

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.DeterministicTransport ----
namespace OAI

namespace TwoWayComplementation

theorem TwoNFA.Deterministic.reindex {Sigma Q Q' : Type*} {A : TwoNFA Sigma Q}
    (hA : A.Deterministic) (e : Q ≃ Q') : (A.reindex e).Deterministic := by
  intro q symbol a ha b hb
  have h := hA (e.symm q) symbol ha hb
  apply Prod.ext
  · exact e.symm.injective (congrArg (fun t : Q × Fin 3 => t.1) h)
  · exact congrArg (fun t : Q × Fin 3 => t.2) h

theorem TwoNFA.Deterministic.pullAlphabet {Sigma Gamma Q : Type*} {A : TwoNFA Gamma Q}
    (hA : A.Deterministic) (f : Sigma → Gamma) : (A.pullAlphabet f).Deterministic := by
  intro q symbol
  exact hA q (Sum.map id f symbol)

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationBridge ----
namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness
open scoped SetRel

/-- Both products compose in path order, including the identity for the empty word. -/
theorem relationProduct_map {H : Type*} (w : List (BRel H)) :
    relationProduct (w.map (relationEquiv H)) = relationEquiv H w.prod := by
  induction w with
  | nil => rfl
  | cons R w ih =>
    change relationEquiv H R ○ relationProduct (w.map (relationEquiv H)) =
      relationEquiv H (R * w.prod)
    rw [ih]
    rfl

theorem sourceLanguage_map_iff {H : Type*} (w : List (BRel H)) :
    w.map (relationEquiv H) ∈ sourceLanguage H ↔ BRel.live w := by
  change (relationProduct (w.map (relationEquiv H))).Nonempty ↔ _
  rw [relationProduct_map]
  exact ⟨fun ⟨⟨x, y⟩, h⟩ => ⟨x, y, h⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h⟩⟩

end TwoWayComplementation.CompanionBridge

end OAI

-- ---- from OAI.Combinatorics.Automata.PathNFA ----
namespace OAI

namespace OneWayLiveness

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
lemma relabel_accepts {n : ℕ} (e : Q ≃ Fin n) (positive : Bool) (w : List Alpha) :
    (M.relabel e).Accepts positive w ↔ M.Accepts positive w := by
  have hfor {c c' : Fin (w.length+2) × Fin n} (hs : (M.relabel e).Step w c c') :
      M.Step w (c.1,e.symm c.2) (c'.1,e.symm c'.2) := hs
  have hback {c c' : Config (Q := Q) w} (hs : M.Step w c c') :
      (M.relabel e).Step w (c.1,e c.2) (c'.1,e c'.2) := by
    simpa only [NMachine.Step, Step, relabel, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hs
  unfold NMachine.Accepts Accepts
  constructor
  · rintro ⟨c,hc,ha⟩
    refine ⟨(c.1,e.symm c.2),?_,ha⟩
    cases positive <;> simp only [FiniteRun, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    · simpa only [Function.onFun, relabel, Equiv.symm_apply_apply] using
        hc.lift (fun c => (c.1,e.symm c.2)) (fun _ _ h => hfor h)
    · simpa only [Function.onFun, relabel, Equiv.symm_apply_apply] using
        hc.lift (fun c => (c.1,e.symm c.2)) (fun _ _ h => hfor h)
  · rintro ⟨c,hc,ha⟩
    refine ⟨(c.1,e c.2),?_,by simpa only [relabel, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using ha⟩
    cases positive <;> simp only [FiniteRun, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    · exact hc.lift (fun c => (c.1,e c.2)) (fun _ _ h => hback h)
    · exact hc.lift (fun c => (c.1,e c.2)) (fun _ _ h => hback h)

lemma relabel_noLeft {n : ℕ} (e : Q ≃ Fin n)
    (hm : ∀ q b q', (q',.left) ∉ M.transition q b) : (M.relabel e).NoLeft :=
  fun q b q' => hm (e.symm q) b (e.symm q')
end NMachineOn

namespace PathNFA
variable {H : Type}
end PathNFA

/-- The explicit path automaton has h+3 states, including the unused rejector.
It accepts only after at least two transitions, so both conventions agree. -/
theorem small_nfa (h : ℕ) :
    ∃ N : NMachine (Alphabet h) (h+3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (OWL h) := by
  classical
  let e : PathNFA.State (Fin h) ≃ Fin (h+3) := Fintype.equivFinOfCardEq (by
    simp only [PathNFA.State, Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_bool])
  refine ⟨PathNFA.machine.relabel e, PathNFA.machine.relabel_noLeft e PathNFA.rules_noLeft, ?_⟩
  intro positive w
  exact (PathNFA.machine.relabel_accepts e positive w).trans (PathNFA.accepts_iff positive w)

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Main ----
namespace OAI

namespace OneWayLiveness

/-- The one-way nondeterministic upper bound and two-way deterministic lower bound,
under both acceptance conventions. -/
theorem main_theorem (h : ℕ) (hh : 2 ≤ h) :
    (∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (OWL h)) ∧
    (∀ (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s),
      D.Recognizes positive (OWL h) →
      2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2) :=
  ⟨small_nfa h,deterministic_lower_bound h hh⟩

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.DeterministicBound ----
namespace OAI

namespace TwoWayComplementation

namespace CompanionBridge

/-- A state lower bound for every deterministic recognizer of relation liveness. -/
theorem deterministic_bound (h s : ℕ) (hh : 2 ≤ h)
    (D : TwoNFA (SetRel (Fin h) (Fin h)) (Fin s))
    (hdet : D.Deterministic) (hD : D.language = sourceLanguage (Fin h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + 1) ^ 2 := by
  let A := D.pullAlphabet (relationEquiv (Fin h))
  have ha : A.Deterministic := hdet.pullAlphabet _
  apply (OneWayLiveness.main_theorem h hh).2 false s (toDMachine A ha)
  intro w
  rw [toDMachine_accepts]
  change w ∈ (D.pullAlphabet (relationEquiv (Fin h))).language ↔ _
  rw [D.pullAlphabet_language, hD]
  exact sourceLanguage_map_iff w

end CompanionBridge

/-- Deterministic lower bound with arbitrary finite state types. -/
theorem deterministic_liveness_lower_bound (n : ℕ) (hn : 131 ≤ n)
    (Q : Type*) [Fintype Q]
    (D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q)
    (hdet : D.Deterministic) (hD : D.language = sourceLanguage (Fin (n - 2))) :
    (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ) := by
  have hb := CompanionBridge.deterministic_bound (n - 2) (Fintype.card Q) (by omega)
    (D.reindex (Fintype.equivFin Q)) (hdet.reindex _) (by
      rw [TwoNFA.reindex_language, hD])
  apply deterministic_rate n (Fintype.card Q) hn
  simpa only [Nat.sub_sub, Nat.reduceAdd] using hb

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ExplicitFamily ----
namespace OAI

namespace TwoWayComplementation

/-- Both lower bounds hold for the same n-state liveness witness. -/
theorem explicit_family_main (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) ∧
      (131 ≤ n → ∀ (Q : Type*) [Fintype Q],
        ∀ D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        D.Deterministic → D.language = A.language →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ)) := by
  obtain ⟨A, hA, hcomp⟩ := explicit_complementation_family n hn
  refine ⟨A, hA, hcomp, ?_⟩
  intro hn Q _ D hdet hD
  exact deterministic_liveness_lower_bound n hn Q D hdet (hD.trans hA)

end TwoWayComplementation

end OAI

-- ---- mission target ----
open OAI OAI.TwoWayComplementation
open scoped SetRel

namespace OAI
namespace TwoWayComplementation
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) ∧
      (131 ≤ n → ∀ (Q : Type*) [Fintype Q],
        ∀ D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        D.Deterministic → D.language = A.language →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ)) := by
  first
    | exact OAI.TwoWayComplementation.explicit_family_main n hn
    | exact OAI.TwoWayComplementation.explicit_family_main
    | (apply OAI.TwoWayComplementation.explicit_family_main <;> assumption)
    | (intros; apply OAI.TwoWayComplementation.explicit_family_main <;> assumption)
end TwoWayComplementation
end OAI
