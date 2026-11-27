-- Prove2me | solution 1 for GlobalTheory.RegSS.pointsAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:24:19.274917+00:00
-- url     : https://prove2.me/submissions/f1752b19-c023-4eaf-b4ac-69b4d2a76200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorInvolutionAdjoint
import Theorems.Thm_GlobalTheory_RegSS_pointsAdjoint_toMat_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_adj_eq_iff
import Theorems.Thm_GlobalTheory_RegSS_adj_add
import Theorems.Thm_GlobalTheory_RegSS_adj_map
import Theorems.Thm_GlobalTheory_RegSS_adj_smul
import Theorems.Thm_GlobalTheory_RegSS_adj_zero
import Theorems.Thm_GlobalTheory_RegSS_inclE_conj
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
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution : PointsAdjoint := by
  intro F E _ _ _ _ n _ _ σ J γ h R _ _ u
  induction u using TensorProduct.induction_on with
  | zero => simp [adj_zero]
  | tmul a b =>
    have ha := (adj_eq_iff _ h.nondeg _ _).2 a.2
    have hc : lConj σ J (γ : Matrix n n E) R (a ⊗ₜ b) = a ⊗ₜ sigR σ R b := rfl
    rw [hc, pointsAdjoint_toMat_tmul,
      pointsAdjoint_toMat_tmul, adj_smul,
      adj_map (σ : E →+* E) (sigR σ R) (inclE (F := F) R) (inclE_conj σ R) h.nondeg, ha]
  | add a b ha hb => rw [map_add, map_add, map_add, adj_add, ha, hb]
end GlobalTheory.RegSS
