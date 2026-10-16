-- Prove2me | solution 1 for OAI.Solenoidal.travelProgram_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:21:19.603538+00:00
-- url     : https://prove2.me/submissions/d2b3431f-d5b7-4a3d-a3af-d3bb6e99f16a

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean:L292-L304
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.travelProgram_on. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization

-- ---- from OAI.MathematicalPhysics.SheetFlows.Profiles ----
namespace OAI

/-! SheetFlows profiles. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

open Filter
open scoped Topology

theorem plateau_one {h d s : ℝ} (hd : 0 < d) (hs : |s| ≤ h + d / 2) :
    plateau h d s = 1 := by
  rcases abs_le.mp hs with ⟨hl, hu⟩
  have h₁ : 1 ≤ 2 * (s + h + d) / d := (le_div_iff₀ hd).mpr (by linarith)
  have h₂ : 1 ≤ 2 * (h + d - s) / d := (le_div_iff₀ hd).mpr (by linarith)
  simp only [plateau, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂, mul_one]

theorem Cprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Cprofile h d c s = plateau h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu) hs

theorem Cprofile_one {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : |s - c| ≤ h + d / 2) : Cprofile h d c s = 1 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_one hd hsc

theorem Cprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Cprofile h d c s = 0 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_zero hd hsc

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Localization ----
namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

variable (d : Collar)

theorem horizontalPulse_field (j : Fin 2) (x : Space) :
    (horizontalPulse d j).field x =
      (Cprofile 0 d.size 5 (x 2) - Cprofile 0 d.size 8 (x 2)) • basis j.castSucc := by
  simp [horizontalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem horizontalPulse_on (j : Fin 2) {x : Space} (hx : x 2 = 5) :
    (horizontalPulse d j).field x = basis j.castSucc := by
  have h₅ : Cprofile 0 d.size 5 5 = 1 := by
    apply Cprofile_one d.positive <;> norm_num <;> linarith [d.small, d.positive]
  have h₈ : Cprofile 0 d.size 8 5 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  simp only [horizontalPulse_field, hx, h₅, h₈, sub_zero, one_smul]

theorem travelProgram_on (δ : Plane) (x y : ℝ) :
    runProgram (travelProgram d δ) ![x,y,5] = ![x+δ 0,y+δ 1,5] := by
  have h₀ : ((horizontalPulse d 0).scale (δ 0)).apply ![x,y,5] = ![x+δ 0,y,5] := by
    simp only [StationaryPulse.apply, StationaryPulse.scale_field,
      horizontalPulse_on d 0 (by rfl : (![x,y,5] : Space) 2 = 5)]
    ext i; fin_cases i <;> simp [basis]
  have h₁ : ((horizontalPulse d 1).scale (δ 1)).apply ![x+δ 0,y,5] = ![x+δ 0,y+δ 1,5] := by
    simp only [StationaryPulse.apply, StationaryPulse.scale_field,
      horizontalPulse_on d 1 (by rfl : (![x+δ 0,y,5] : Space) 2 = 5)]
    ext i; fin_cases i <;> simp [basis]
  change ((horizontalPulse d 1).scale (δ 1)).apply
    (((horizontalPulse d 0).scale (δ 0)).apply ![x,y,5]) = _
  rw [h₀, h₁]

end Solenoidal
end
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Solenoidal.travelProgram_on := @_root_.OAI.Solenoidal.travelProgram_on
