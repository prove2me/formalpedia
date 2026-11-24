-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.val_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:47.988818+00:00
-- url     : https://prove2.me/submissions/5dffb3af-b160-4851-b333-34aa1da07113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResVal
namespace GlobalTheory.UnitLemma.Unr.ResVal
theorem _root_.solution {K : UQ} (k : ℕ) (x : K.E) : val K.O ((-1) ^ k * x) = val K.O x := by
  rcases neg_one_pow_eq_or K.E k with h | h <;> simp [h, val, Valuation.map_neg]
end GlobalTheory.UnitLemma.Unr.ResVal
