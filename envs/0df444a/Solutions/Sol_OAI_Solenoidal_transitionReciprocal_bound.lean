-- Prove2me | solution 1 for OAI.Solenoidal.transitionReciprocal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:26:12.805982+00:00
-- url     : https://prove2.me/submissions/155f0dac-c9e8-47a7-872a-9d68d769f870

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/JetCalculus.lean:L75-L94
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.transitionReciprocal_bound. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.SheetFlows.JetCalculus ----
namespace OAI

/-! SheetFlows jet calculus. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal

theorem transitionReciprocal_bound (x : ℝ) : |transitionReciprocal x| ≤ 16 := by
  have hhalf : expNegInvGlue (1/2) = Real.exp (-2) := by norm_num [expNegInvGlue]
  have hlow : Real.exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1-x) := by
    rw [← hhalf]
    rcases le_or_gt (1/2:ℝ) x with hx | hx
    · exact (expNegInvGlue.monotone hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
    · exact (expNegInvGlue.monotone (by linarith : (1/2:ℝ) ≤ 1-x)).trans
        (le_add_of_nonneg_left (expNegInvGlue.nonneg _))
  have hpos := Real.smoothTransition.pos_denom x
  have hb : (expNegInvGlue x + expNegInvGlue (1-x))⁻¹ ≤ Real.exp 2 := by
    calc
      _ ≤ (Real.exp (-2))⁻¹ := inv_anti₀ (Real.exp_pos _) hlow
      _ = Real.exp 2 := by rw [Real.exp_neg, inv_inv]
  have he : Real.exp (2:ℝ) < 9 := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos (1:ℝ)
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  rw [transitionReciprocal, abs_of_pos (inv_pos.mpr hpos)]
  linarith

namespace JetExpr

end JetExpr

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial


theorem solution : type_of% @_root_.OAI.Solenoidal.transitionReciprocal_bound := @_root_.OAI.Solenoidal.transitionReciprocal_bound
