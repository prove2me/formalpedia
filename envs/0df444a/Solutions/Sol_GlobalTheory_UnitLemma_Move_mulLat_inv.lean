-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.mulLat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:04.22581+00:00
-- url     : https://prove2.me/submissions/4d7ee2c6-47ef-48de-b70d-2d2dc3e6edd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Move_mem_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Move
theorem _root_.solution (M : Submodule K.O B.A) (y : B.Aˣ) :
    mulLat K.O ((y⁻¹ : B.Aˣ) : B.A) (mulLat K.O (y : B.A) M) = M := by
  ext z
  rw [mem_mulLat, mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
end GlobalTheory.UnitLemma.Move
