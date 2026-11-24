-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.exists_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:30:33.174333+00:00
-- url     : https://prove2.me/submissions/a469f362-568d-4df2-9164-74542d37a588

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {x y : L} (h : y + σ y + x * σ x = 0) :
    ∃ g : GU σ 3, mat g = Heisenberg₂ σ x y := by
  apply exists_mat
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  simp only [P.fSatake_cTJ, r0, r1, r2]
  fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, antiJ, hσ]
  linear_combination h
end GlobalTheory.SatakeWeyl.Heis
