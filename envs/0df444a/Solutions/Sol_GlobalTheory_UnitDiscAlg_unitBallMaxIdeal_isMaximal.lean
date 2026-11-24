-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.unitBallMaxIdeal_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:58.157645+00:00
-- url     : https://prove2.me/submissions/4e593f1b-de00-488c-aabb-8a4debb5c3e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.UnitDiscAlg
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution : (unitBallMaxIdeal E).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    have h' : ‖((1 : E))‖ < 1 := h
    simp at h'
  · intro J x _ hx hxJ
    have hx1 : ¬ ‖(x : E)‖ < 1 := hx
    have hx2 : ‖(x : E)‖ ≤ 1 := x.2
    have hn : ‖(x : E)‖ = 1 := le_antisymm hx2 (not_lt.mp hx1)
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv : ‖(x : E)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
    have hmem := J.mul_mem_left ⟨(x : E)⁻¹, hinv⟩ hxJ
    convert hmem using 1
    apply Subtype.ext
    exact (inv_mul_cancel₀ hx0).symm
end GlobalTheory.UnitDiscAlg
