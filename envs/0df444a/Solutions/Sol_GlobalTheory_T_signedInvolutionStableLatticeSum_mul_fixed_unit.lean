-- Prove2me | solution 1 for GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:32.597254+00:00
-- url     : https://prove2.me/submissions/742853be-4571-4f93-995b-ebc819eef0ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnitStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Move_HH_mul_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A), B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  first | exact @GlobalTheory.UnitLemma.Move.HH_mul_unit | exact GlobalTheory.UnitLemma.Move.HH_mul_unit | (intros; apply GlobalTheory.UnitLemma.Move.HH_mul_unit <;> assumption)
end _root_.GlobalTheory.T
