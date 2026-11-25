-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.val_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:36.864253+00:00
-- url     : https://prove2.me/submissions/f6a13cc2-21b2-4580-bf95-e80c02f9965a

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
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_ResVal_val_mul__6c19df7bd17f
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_unit
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IsUnrExt_ne_zero


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
theorem _root_.solution {K : UQ} (x : K.E) (u : K.O) (hu : IsUnit u) :
    val K.O (x * algebraMap K.O K.E u) = val K.O x := by
  by_cases hx : x = 0
  · simp [hx]
  have hu0 : algebraMap K.O K.E u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hu.ne_zero
  rw [val_mul' hx hu0, GlobalTheory.UnitLemma.Orbit.val_unit u hu, add_zero]
end GlobalTheory.UnitLemma.Unr.ResVal
