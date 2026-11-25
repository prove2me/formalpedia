-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.defect_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:40.321047+00:00
-- url     : https://prove2.me/submissions/7dca3149-0f1e-439d-84a3-be9ccd5eecd0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_nonneg
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_add_le
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_neg
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_mul_le
import Theorems.Thm_GlobalTheory_ExpBallSandwich_exp_strict
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.ExpBallSandwich
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.ExpBallSandwich
theorem _root_.solution (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by
  obtain ⟨ρ, hρ, h⟩ := exp_strict (n := n) η hη
  refine ⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩
  rw [lt_min_iff] at hX hY hZ
  have h0 : sumAbs (0 : Matrix n n ℂ) < ρ := by simpa [sumAbs] using hρ
  have key : ∀ W : Matrix n n ℂ, sumAbs W < ρ →
      sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧
      sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W := by
    intro W hW
    have h1 := h W 0 hW h0
    rw [NormedSpace.exp_zero, sub_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 := sumAbs_add_le (NormedSpace.exp W - 1 - W) W
    rw [sub_add_cancel] at h2
    have := sumAbs_nonneg W
    nlinarith
  have e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) +
      ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) := by
    rw [he]; noncomm_ring
  have a1 := h Y X hY.1 hX.1
  have a2 := (key Z hZ.1).1
  have a3 := (key Z hZ.1).2
  have a4 : sumAbs (NormedSpace.exp X - 1) ≤ η := by linarith [(key X hX.1).2, hX.2]
  have a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z) :=
    (sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)
  rw [e]
  refine (sumAbs_add_le _ _).trans ?_
  rw [sumAbs_neg]
  have a6 := sumAbs_add_le (NormedSpace.exp Z - 1 - Z)
    ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))
  linarith
end GlobalTheory.ExpBallSandwich
