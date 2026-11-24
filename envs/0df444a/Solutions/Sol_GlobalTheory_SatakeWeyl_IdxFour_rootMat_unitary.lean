-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.rootMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:33.13408+00:00
-- url     : https://prove2.me/submissions/2066c5c3-ecf7-4a70-8cb9-76275bd4355f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
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
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.IdxFour
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (x : L) :
    cT σ (rootMat σ x) * antiJ L 4 * rootMat σ x = antiJ L 4 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [P.fSatake_cTJ, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]
end GlobalTheory.SatakeWeyl.IdxFour
