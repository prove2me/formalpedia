-- Prove2me | solution 1 for OAI.Solenoidal.periodic_integral_divergence_zero_C1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:04:29.914368+00:00
-- url     : https://prove2.me/submissions/49b1060b-c862-4630-b10b-c6426479818c

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/ClassicalRegularity.lean:L103-L123
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.periodic_integral_divergence_zero_C1. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.SheetFlows.ScheduledForce ----
namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem cell_ae_eq_Icc : fundamentalCell =ᵐ[volume] Set.Icc (0 : Space) (fun _ => 10) :=
  Measure.univ_pi_Ico_ae_eq_Icc

theorem face_front_eq_back_deck (j : Fin 3) (y : Fin 2 → ℝ) :
    j.insertNth (10 : ℝ) y = j.insertNth 0 y + deck (Pi.single j 1) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp [deck]
  · simp [deck]

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity ----
namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem periodic_integral_divergence_zero_C1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Fin 3 → Space → E) (hg : ∀ j, TorusC1 (g j)) :
    (∫ x in fundamentalCell, ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) = 0 := by
  rw [setIntegral_congr_set cell_ae_eq_Icc]
  have hc := continuous_finsetSum Finset.univ (fun j _ => (hg j).continuous_partial j)
  simp only [basis] at *
  rw [integral_divergence_of_hasFDerivAt_off_countable' (0 : Space) (fun _ => 10)
    (fun _ => by norm_num) g (fun j => fderiv ℝ (g j)) ∅ Set.countable_empty
    (fun j => (hg j).differentiable.continuous.continuousOn)
    (fun x _ j => (hg j).differentiable x |>.hasFDerivAt)
    hc.integrableOn_Icc]
  apply Finset.sum_eq_zero
  intro j _
  have he : (fun y : Fin 2 → ℝ => g j (j.insertNth 10 y)) =
      (fun y : Fin 2 → ℝ => g j (j.insertNth 0 y)) := by
    funext y
    rw [face_front_eq_back_deck]
    exact (hg j).periodic _ _
  change (∫ y in Set.Icc _ _, g j (j.insertNth 10 y)) -
    (∫ y in Set.Icc _ _, g j (j.insertNth 0 y)) = 0
  rw [he, sub_self]

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.periodic_integral_divergence_zero_C1 := @_root_.OAI.Solenoidal.periodic_integral_divergence_zero_C1
