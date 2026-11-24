-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.inDual_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:03.51493+00:00
-- url     : https://prove2.me/submissions/b5e327d9-9504-420e-929a-756000e2e3fb

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
theorem _root_.solution (M : Submodule K.O B.A) (y : B.Aˣ) (t : B.A) :
    InDual B t (mulLat K.O (y : B.A) M) ↔ InDual B ((y : B.A) * t) M := by
  unfold InDual
  constructor
  · intro h z hz
    have := h ((y : B.A) * z) (by rw [mem_mulLat, Units.inv_mul_cancel_left]; exact hz)
    have e : t * ((y : B.A) * z) = (y : B.A) * t * z := by ring
    rwa [e] at this
  · intro h z hz
    rw [mem_mulLat] at hz
    have := h _ hz
    have e : (y : B.A) * t * (((y⁻¹ : B.Aˣ) : B.A) * z) = t * z := by
      rw [mul_comm (y : B.A) t, mul_assoc, Units.mul_inv_cancel_left]
    rwa [e] at this
end GlobalTheory.UnitLemma.Move
