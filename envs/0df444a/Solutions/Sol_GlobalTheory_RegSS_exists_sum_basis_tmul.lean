-- Prove2me | solution 1 for GlobalTheory.RegSS.exists_sum_basis_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:21:47.837798+00:00
-- url     : https://prove2.me/submissions/87898992-0133-4401-870c-2319b2e5a875

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
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
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b x
  exact ⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩
end GlobalTheory.RegSS
