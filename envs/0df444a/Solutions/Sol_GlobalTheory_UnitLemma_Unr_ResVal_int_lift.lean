-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.int_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:14.366284+00:00
-- url     : https://prove2.me/submissions/9988b34b-7fe7-4200-9335-473bd5a3c339

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
import Theorems.Thm_GlobalTheory_T_exists_integerMap_isIntegral_unramifiedInvolutionExt


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt
end GlobalTheory.UnitLemma.Unr.ResVal
