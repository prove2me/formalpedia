-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.monic_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:46.120385+00:00
-- url     : https://prove2.me/submissions/c653f529-8abd-4c7c-b5ed-528f5c8de328

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
theorem _root_.solution {F : Type} [Field F] (a : F) (n : ℕ) (f : F[X]) (hf : f.Monic) (h : f ∣ (X - C a) ^ n) :
    f = (X - C a) ^ f.natDegree := by
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C a) n).1 h
  have e := eq_of_monic_of_associated hf ((monic_X_sub_C a).pow i) hi
  rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]
end GlobalTheory.UnitLemma.Unr.ResVal
