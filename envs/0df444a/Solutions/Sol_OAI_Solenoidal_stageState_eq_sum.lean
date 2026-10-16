-- Prove2me | solution 1 for OAI.Solenoidal.stageState_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:15:29.971221+00:00
-- url     : https://prove2.me/submissions/b7f3e1f0-37f2-4665-96bf-10de5d60f916

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean:L33-L57
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.stageState_eq_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories

-- ---- from OAI.MathematicalPhysics.SheetFlows.Trajectories ----
namespace OAI

/-! SheetFlows trajectories. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem stageState_succ {m : ℕ} (v : Fin m → Space → Space) (a : Space) (i : Fin m) :
    stageState v a (i.val + 1) = stageState v a i.val + stageIncrement v a i := by
  rw [stageState, stageField_fin]
  rfl

theorem stageState_eq_sum {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {n : ℕ} (hn : n ≤ m) :
    stageState v a n = a + ∑ i : Fin m, if i.val < n then stageIncrement v a i else 0 := by
  induction n with
  | zero => simp [stageState]
  | succ n ih =>
    have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have he (i : Fin m) :
        (if i.val < n + 1 then stageIncrement v a i else 0) =
        (if i.val < n then stageIncrement v a i else 0) +
        (if i = ⟨n, hnm⟩ then stageIncrement v a i else 0) := by
      by_cases hi : i.val < n
      · have hne : i ≠ ⟨n, hnm⟩ := by intro h; simp [h] at hi
        simp [hi, Nat.lt_succ_of_lt hi, hne]
      · by_cases hie : i = ⟨n, hnm⟩
        · subst i
          simp
        · have hin : ¬i.val < n + 1 := by
            have hv : i.val ≠ n := by simpa [Fin.ext_iff] using hie
            omega
          simp [hi, hie, hin]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← add_assoc, ← ih (Nat.le_of_succ_le hn), ← stageState_succ v a ⟨n, hnm⟩]

end Solenoidal

end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.stageState_eq_sum := @_root_.OAI.Solenoidal.stageState_eq_sum
