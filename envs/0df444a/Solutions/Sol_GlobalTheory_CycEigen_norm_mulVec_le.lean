-- Prove2me | solution 1 for GlobalTheory.CycEigen.norm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:31:51.58052+00:00
-- url     : https://prove2.me/submissions/3313ee24-4d89-4610-be6e-f775252c706b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycEigen
theorem _root_.solution {r : ℕ} (B : Matrix (Fin r) (Fin r) C) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (v : Fin r → C) (a : Fin r) : ‖B.mulVec v a‖ ≤ c * ‖v‖ := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc
end GlobalTheory.CycEigen
