-- Prove2me | solution 1 for GlobalTheory.TwIntegral.isUnit_of_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:22.188813+00:00
-- url     : https://prove2.me/submissions/59abfe5d-02a6-4c63-ad2d-8cdbe254a703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.TwIntegral
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
open Matrix
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.TwIntegral
namespace _root_.GlobalTheory.TwIntegral
theorem _root_.solution {A : Matrix (Fin n) (Fin n) E} (hd : ‖A.det‖ = 1) :
    IsUnit A := by
  rw [isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  rw [h, norm_zero] at hd
  exact zero_ne_one hd
end _root_.GlobalTheory.TwIntegral
end GlobalTheory.TwIntegral
