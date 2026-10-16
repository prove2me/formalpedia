-- Prove2me | solution 1 for OAI.Solenoidal.scheduledPulse_integer_collar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:23.280975+00:00
-- url     : https://prove2.me/submissions/226730e6-67fe-4b0a-9abe-7673589fe6f5

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Clocks.lean:L186-L203
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.scheduledPulse_integer_collar. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks

-- ---- from OAI.MathematicalPhysics.SheetFlows.Clocks ----
namespace OAI

/-! SheetFlows clocks. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem scheduledPulse_integer_collar {m : ℕ} (i : Fin m)
    (n : ℤ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    scheduledPulse m i t = 0 := by
  rcases slot_bounds i with ⟨ha, hab, hb⟩
  change (∑' k : ℤ, localPulse _ _ (t - 1 * k)) = 0
  suffices h : ∀ k : ℤ, localPulse (slotLeft m i) (slotRight m i) (t - 1 * k) = 0 by
    simp only [h, tsum_zero]
  intro k
  rcases abs_lt.mp ht with ⟨ht₀, ht₁⟩
  by_cases hk : n ≤ k
  · have hk' : (n : ℝ) ≤ k := by exact_mod_cast hk
    apply localPulse_zero_left hab
    simp only [one_mul]
    linarith
  · have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
    apply localPulse_zero_right hab
    simp only [one_mul]
    linarith

end Solenoidal
end
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.scheduledPulse_integer_collar := @_root_.OAI.Solenoidal.scheduledPulse_integer_collar
