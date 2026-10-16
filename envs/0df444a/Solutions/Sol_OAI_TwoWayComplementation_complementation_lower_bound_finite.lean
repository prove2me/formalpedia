-- Prove2me | solution 1 for OAI.TwoWayComplementation.complementation_lower_bound_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:42:23.322627+00:00
-- url     : https://prove2.me/submissions/5c9adfc1-0a9e-4f32-805e-5943ea5fa6df

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Main.lean:L30-L43
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TwoWayComplementation.complementation_lower_bound_finite.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TwoWayComplementation_complementation_lower_bound_finite) verbatim and is proved by it.
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
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_reindex_language
import Theorems.Thm_OAI_TwoWayComplementation_complementation_lower_bound

-- ---- from OAI.Combinatorics.TwoWayAutomata.Main ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The real-valued lower bound for arbitrary finite target state sets. -/
theorem complementation_lower_bound_finite (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ (Q : Type*) [Fintype Q], ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ) := by
  obtain ⟨A, hA⟩ := complementation_lower_bound n hn
  refine ⟨A, ?_⟩
  intro Q _ B hB
  have hbound := hA (Fintype.card Q) (B.reindex (Fintype.equivFin Q)) (by
    rw [TwoNFA.reindex_language, hB])
  have hreal : (2 : ℝ) ^ ((n - 4) / 127) ≤ 2 * ((Fintype.card Q : ℝ) + 1) := by
    exact_mod_cast hbound
  linarith

end TwoWayComplementation

end OAI

-- ---- mission target ----
open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ (Q : Type*) [Fintype Q], ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ) := by
  first
    | exact OAI.TwoWayComplementation.complementation_lower_bound_finite n hn
    | exact OAI.TwoWayComplementation.complementation_lower_bound_finite
    | (apply OAI.TwoWayComplementation.complementation_lower_bound_finite <;> assumption)
    | (intros; apply OAI.TwoWayComplementation.complementation_lower_bound_finite <;> assumption)
