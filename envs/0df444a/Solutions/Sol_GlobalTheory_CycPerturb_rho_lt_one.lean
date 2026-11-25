-- Prove2me | solution 1 for GlobalTheory.CycPerturb.rho_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:46.157401+00:00
-- url     : https://prove2.me/submissions/cb16a507-f9d8-4bc0-affd-dcc829f515da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
end GlobalTheory.CycPerturb
