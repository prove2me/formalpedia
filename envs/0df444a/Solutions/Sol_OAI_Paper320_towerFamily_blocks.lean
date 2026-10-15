-- Prove2me | solution 1 for OAI.Paper320.towerFamily_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:35:23.583135+00:00
-- url     : https://prove2.me/submissions/8eb2023e-f6a0-4ca2-8bee-2aa9493bc714

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Tower.lean:L133-L155
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.towerFamily_blocks. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveBlocks ----
namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_rowLift_same {k r : ℕ} {I : Type}
    (i : Fin k) (B : Finset I) (c : Fin r) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) i c =
      flip (fun _ => false) B := by
  funext a
  simp [recursiveChild, flip]

theorem recursiveChild_rowLift_other {k r : ℕ} {I : Type}
    (i j : Fin k) (B : Finset I) (c : Fin r) (hji : j ≠ i) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) j c =
      fun _ => false := by
  funext a
  simp [recursiveChild, flip, hji]

theorem recursiveFamily_rowLift {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hzero : ∀ q, F q (fun _ => false) = false) (B : Finset I)
    (hB : ∀ q, F q (flip (fun _ => false) B) = true) (i : Fin k) (q : Fin h) :
    recursiveFamily T label F q (flip (fun _ => false) (rowLift i B)) = true := by
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  refine ⟨i, (rowClause_eq_true_iff _ _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro c
    rw [recursiveChild_rowLift_same]
    exact hB _
  · intro j hij
    rw [recursiveChild_rowLift_other _ _ _ _ (T.ne_of_adj hij).symm]
    exact hzero _

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tower ----
namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by
  induction n generalizing h with
  | zero =>
    change ∀ b q, base h q (flip (fun _ => false) (blocks b)) = true
    simpa only [Nat.add_zero] using hblocks
  | succ n ih =>
    intro b q
    have he : (h + 1) + n = h + (n + 1) := by omega
    have hz : ∀ q, base ((h + 1) + n) q (fun _ => false) = false := by
      rw [he]
      exact hzero
    have hb : ∀ b q, base ((h + 1) + n) q (flip (fun _ => false) (blocks b)) = true := by
      rw [he]
      exact hblocks
    exact recursiveFamily_rowLift T label _
      (towerFamily_zero T label base hr n (h + 1) hz)
      (towerBlocks blocks n b.2) (ih (h + 1) hz hb b.2) b.1 q

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical

theorem solution {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by
  first
    | exact OAI.Paper320.towerFamily_blocks T label base blocks hr n h hzero hblocks
    | exact OAI.Paper320.towerFamily_blocks
    | (apply OAI.Paper320.towerFamily_blocks <;> assumption)
    | (intros; apply OAI.Paper320.towerFamily_blocks <;> assumption)
