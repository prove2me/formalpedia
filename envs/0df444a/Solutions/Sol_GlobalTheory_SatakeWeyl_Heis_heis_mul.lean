-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.heis_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:22.424347+00:00
-- url     : https://prove2.me/submissions/2c9194c3-27f5-4ba2-96e4-616dfb441021

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
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
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (x y x' y' : L) :
    Heisenberg₂ σ x y * Heisenberg₂ σ x' y' = Heisenberg₂ σ (x + x') (y + y' - x * σ x') := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [Heisenberg₂] <;> ring
end GlobalTheory.SatakeWeyl.Heis
