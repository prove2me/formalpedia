-- Prove2me | solution 1 for OAI.Solenoidal.verticalPulse_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:32:55.93923+00:00
-- url     : https://prove2.me/submissions/4be83a75-5865-4688-b71c-b994474c4693

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/FormulaProfiles.lean:L90-L104
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.verticalPulse_formula. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Theorems.Thm_OAI_Solenoidal_tensorVelocity_formula

-- ---- from OAI.MathematicalPhysics.SheetFlows.Localization ----
namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

variable (d : Collar)

theorem rect_support_chart (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) :
    R.halfWidth j + d.size ≤ R.center j + s ∧
      R.center j + s + (R.halfWidth j + d.size) ≤ 10 := by
  have hw := R.halfWidth_le_half hR j
  have hc := R.center_bounds hR j
  constructor <;> linarith [d.small, hs.1, hs.2]

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.FormulaProfiles ----
namespace OAI

/-! SheetFlows formula profiles. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace RationalParameter

theorem rat (q : ℚ) : RationalParameter (q:ℝ) := ⟨q,rfl⟩
theorem ofNat (n : ℕ) : RationalParameter (n:ℝ) := ⟨n,by simp⟩
theorem add {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b,by simp⟩
theorem sub {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a-b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a-b,by simp⟩
theorem div {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a/b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a/b,by simp⟩
end RationalParameter

theorem Rectangle.center_rational (R : Rectangle) (j : Fin 2) :
    RationalParameter (R.center j) :=
  ((RationalParameter.rat _).add (.rat _)).div (.ofNat 2)

theorem Rectangle.halfWidth_rational (R : Rectangle) (j : Fin 2) :
    RationalParameter (R.halfWidth j) :=
  ((RationalParameter.rat _).sub (.rat _)).div (.ofNat 2)

theorem Cprofile_hasJet {h d c : ℝ}
    (hh : RationalParameter h) (hd : RationalParameter d) (hc : RationalParameter c)
    (hpos : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    Nonempty (PeriodicJet 10 (Cprofile h d c)) := by
  obtain ⟨h,rfl⟩ := hh; obtain ⟨d,rfl⟩ := hd; obtain ⟨c,rfl⟩ := hc
  exact ⟨Cprofile_jet h d c (by exact_mod_cast hpos) (by exact_mod_cast hl) (by exact_mod_cast hu)⟩

namespace StationaryPulse

theorem rationalFormula_tensor (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j, Function.Periodic (g j) 10)
    (hi : ∀ s, g i s = 1) (j : Fin 3)
    (hz : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0)
    (hr : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    (tensor i g hsm hp hi j hz).RationalFormula := tensorVelocity_formula i g hr

end StationaryPulse

variable (d : Collar) (hd : RationalParameter d.size)
include hd

theorem verticalPulse_formula (R : Rectangle) (hR : R.inCodingSquare) {s : ℝ}
    (hs : s ∈ Set.Icc 0 4) (hsr : RationalParameter s) :
    (verticalPulse d R hR s).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  have h (j : Fin 2) (v : ℝ) (hvr : RationalParameter v) (hv : v ∈ Set.Icc 0 4) :
      Nonempty (PeriodicJet 10 (Cprofile (R.halfWidth j) d.size (R.center j+v))) :=
    Cprofile_hasJet (R.halfWidth_rational j) hd ((R.center_rational j).add hvr)
      d.positive (rect_support_chart d R hR j hv).1 (rect_support_chart d R hR j hv).2
  intro j
  fin_cases j
  · exact h 0 s hsr hs
  · obtain ⟨a⟩ := h 1 0 (by exact ⟨0, by norm_num⟩) (by norm_num)
    obtain ⟨b⟩ := h 1 4 (by exact ⟨4, by norm_num⟩) (by norm_num)
    exact ⟨by simpa using a.sub b⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Solenoidal.verticalPulse_formula := @_root_.OAI.Solenoidal.verticalPulse_formula
