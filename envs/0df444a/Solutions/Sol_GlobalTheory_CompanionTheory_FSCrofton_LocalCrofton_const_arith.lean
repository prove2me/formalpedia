-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.const_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:53.353255+00:00
-- url     : https://prove2.me/submissions/157bd415-9458-4bb1-8e8d-7ae1bfd99b44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
namespace GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
theorem _root_.solution (d m n : ℕ) (hn : n = m + 1) (x : ℝ) :
    ENNReal.ofReal (Real.pi ^ (d * m) * (d.factorial : ℝ) * x) =
      ENNReal.ofReal (Real.pi ^ (d * n)) *
        ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * x) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg Real.pi_pos.le _)]
  congr 1
  subst hn
  have hp : (Real.pi ^ d) ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  rw [Nat.mul_succ, pow_add]
  field_simp
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
