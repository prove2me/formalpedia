-- Prove2me | solution 1 for OAI.Solenoidal.scheduleVelocity_at_time
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:01:24.510233+00:00
-- url     : https://prove2.me/submissions/53d7b763-a2f6-49a4-af5b-5c42fe72f29c

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean:L70-L85
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.scheduleVelocity_at_time. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential

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

theorem periodicPulse_on_fraction {a b : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (t : ℝ) :
    periodicPulse a b t = localPulse a b (Int.fract t) := by
  have hp := ((periodicPulse_periodic a b).int_mul ⌊t⌋).sub_eq t
  simp only [mul_one] at hp
  rw [← hp]
  change periodicPulse a b (Int.fract t) = _
  exact periodicPulse_on_chart hab ha hb ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem slot_ordered {m : ℕ} {i j : Fin m} (hij : i < j) :
    slotRight m i < slotLeft m j := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  dsimp [slotLeft, slotRight]
  field_simp
  nlinarith

theorem scheduledPulse_active {m : ℕ} (i : Fin m) {t : ℝ}
    (ht : scheduledPulse m i t ≠ 0) :
    slotLeft m i < Int.fract t ∧ Int.fract t < slotRight m i := by
  rcases slot_bounds i with ⟨ha, hab, hb⟩
  change periodicPulse _ _ t ≠ 0 at ht
  rw [periodicPulse_on_fraction hab (by linarith) (by linarith)] at ht
  constructor
  · exact lt_of_not_ge (fun h => ht (localPulse_zero_left hab h))
  · exact lt_of_not_ge (fun h => ht (localPulse_zero_right hab h))

theorem scheduledPulse_disjoint {m : ℕ} {i j : Fin m} (hij : i ≠ j) (t : ℝ) :
    scheduledPulse m i t = 0 ∨ scheduledPulse m j t = 0 := by
  by_contra h
  push Not at h
  rcases scheduledPulse_active i h.1 with ⟨hi₀, hi₁⟩
  rcases scheduledPulse_active j h.2 with ⟨hj₀, hj₁⟩
  rcases lt_or_gt_of_ne hij with hij | hij
  · linarith [slot_ordered hij]
  · linarith [slot_ordered hij]

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem scheduleVelocity_at_time {m : ℕ} (v : Fin m → Space → Space) (t : ℝ) :
    scheduleVelocity v t = 0 ∨
      ∃ i, scheduleVelocity v t = scheduledPulse m i t • v i := by
  by_cases ht : ∃ i, scheduledPulse m i t ≠ 0
  · obtain ⟨i, hi⟩ := ht
    right
    refine ⟨i, ?_⟩
    funext x
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [(scheduledPulse_disjoint hji t).resolve_right hi, zero_smul]
    · simp
  · left
    push Not at ht
    funext x
    simp [scheduleVelocity, ht]

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.scheduleVelocity_at_time := @_root_.OAI.Solenoidal.scheduleVelocity_at_time
