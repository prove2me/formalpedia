-- Prove2me | solution 1 for OAI.Solenoidal.flatJet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:22:41.98108+00:00
-- url     : https://prove2.me/submissions/a874ba17-138a-4b83-980c-b79c9b1b5b33

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/JetCalculus.lean:L44-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.flatJet_bound. The node keeps its source
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

theorem flatBound_nonneg (p : ℚ[X]) : 0 ≤ flatBound p := by
  apply Finset.sum_nonneg
  intro n _
  positivity

theorem pow_mul_exp_neg_le_factorial {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    z^n * Real.exp (-z) ≤ n.factorial := by
  have h := Real.pow_div_factorial_le_exp z hz n
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hh : z^n ≤ (n.factorial:ℝ)*Real.exp z := by
    simpa [mul_comm] using (div_le_iff₀ hf).mp h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hh

theorem flatJet_bound (p : ℚ[X]) (x : ℝ) : |flatJet p x| ≤ (flatBound p : ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [flatJet, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    exact_mod_cast flatBound_nonneg p
  have hx : 0 < x := lt_of_not_ge hx
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  have he : expNegInvGlue x = Real.exp (-x⁻¹) := by simp [expNegInvGlue,hx.not_ge]
  have hv : (p.map (Rat.castHom ℝ)).eval x⁻¹ =
      ∑ n ∈ p.support, (p.coeff n : ℝ) * (x⁻¹)^n := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum]
    rfl
  rw [flatJet, hv, he, Finset.sum_mul]
  calc
    |∑ n ∈ p.support, (p.coeff n:ℝ)*(x⁻¹)^n*Real.exp (-x⁻¹)|
        ≤ ∑ n ∈ p.support, |(p.coeff n:ℝ)*(x⁻¹)^n*Real.exp (-x⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, (|p.coeff n|:ℝ)*(n.factorial:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hi _), abs_of_pos (Real.exp_pos _)]
      simpa only [Rat.cast_abs, Nat.cast_ofNat, mul_assoc] using
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial hi n) (abs_nonneg (p.coeff n:ℝ))
    _ = (flatBound p:ℝ) := by simp [flatBound]

namespace JetExpr

end JetExpr

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial


theorem solution : type_of% @_root_.OAI.Solenoidal.flatJet_bound := @_root_.OAI.Solenoidal.flatJet_bound
