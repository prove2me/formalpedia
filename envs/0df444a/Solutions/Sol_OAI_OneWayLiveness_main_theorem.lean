-- Prove2me | solution 1 for OAI.OneWayLiveness.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:20:35.436647+00:00
-- url     : https://prove2.me/submissions/b14a1179-72f6-4409-8a3b-7d983902ce8e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Main.lean:L8-L16
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.OneWayLiveness.main_theorem.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_OneWayLiveness_main_theorem) verbatim and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
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
import Theorems.Thm_OAI_OneWayLiveness_PathNFA_accepts_iff
import Theorems.Thm_OAI_OneWayLiveness_deterministic_lower_bound

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

-- ---- mission target ----
open OAI OAI.OneWayLiveness

theorem solution (h : ℕ) (hh : 2 ≤ h) :
    (∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (OWL h)) ∧
    (∀ (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s),
      D.Recognizes positive (OWL h) →
      2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2) := by
  first
    | exact OAI.OneWayLiveness.main_theorem h hh
    | exact OAI.OneWayLiveness.main_theorem
    | (apply OAI.OneWayLiveness.main_theorem <;> assumption)
    | (intros; apply OAI.OneWayLiveness.main_theorem <;> assumption)
