-- Prove2me | solution 1 for OAI.Solenoidal.repeatedPath_on_collar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:16:56.891995+00:00
-- url     : https://prove2.me/submissions/b9570d24-043a-48fb-ac17-2dffe0626d49

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean:L163-L181
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.repeatedPath_on_collar. The node keeps its source
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
import Theorems.Thm_OAI_Solenoidal_stageState_eq_sum

-- ---- from OAI.MathematicalPhysics.SheetFlows.Trajectories ----
namespace OAI

/-! SheetFlows trajectories. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem stageState_final {m : ℕ} (v : Fin m → Space → Space) (a : Space) :
    stageState v a m = a + ∑ i : Fin m, stageIncrement v a i := by
  simpa only [Fin.is_lt, ite_true] using stageState_eq_sum v a (le_refl m)

theorem launchPath_start {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {t : ℝ} (ht : t ≤ 1/4) : launchPath v a t = a := by
  have he (i : Fin m) : pulseClock (slotLeft m i) (slotRight m i) t = 0 :=
    pulseClock_zero (slot_bounds i).2.1 (ht.trans (slot_bounds i).1)
  simp [launchPath, he]

theorem launchPath_finish {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {t : ℝ} (ht : 3/4 ≤ t) : launchPath v a t = stageState v a m := by
  have he (i : Fin m) : pulseClock (slotLeft m i) (slotRight m i) t = 1 :=
    pulseClock_one (slot_bounds i).2.1 ((slot_bounds i).2.2.trans ht)
  simp only [launchPath, he, one_smul, stageState_final]

theorem repeatedPath_on_Ico {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    repeatedPath v a t = launchPath v (periodState v a n) (t - n) := by
  rw [repeatedPath, Nat.floor_eq_on_Ico n t ht]

theorem repeatedPath_on_collar {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    repeatedPath v a t = periodState v a n := by
  obtain ⟨hl, hr⟩ := abs_lt.mp ht
  cases n with
  | zero =>
    have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num at hr; linarith)
    simp only [repeatedPath, hf, Nat.cast_zero, sub_zero, periodState]
    exact launchPath_start v a (by norm_num at hr; linarith)
  | succ n =>
    by_cases hnt : ((n + 1 : ℕ) : ℝ) ≤ t
    · rw [repeatedPath_on_Ico v a (n+1) ⟨hnt, by linarith⟩]
      exact launchPath_start v _ hr.le
    · have htn : t < (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnt
      rw [repeatedPath_on_Ico v a n ⟨by push_cast at hl; linarith, htn⟩]
      change launchPath v (periodState v a n) (t - n) = stageState v (periodState v a n) m
      apply launchPath_finish
      push_cast at hl
      linarith

end Solenoidal

end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.repeatedPath_on_collar := @_root_.OAI.Solenoidal.repeatedPath_on_collar
