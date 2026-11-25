-- Prove2me | solution 1 for GlobalTheory.SA.TransvG.det_fromBlocks_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:07.601025+00:00
-- url     : https://prove2.me/submissions/7a23d9d0-3424-4637-ac90-8363f462aaa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
import Theorems.Thm_GlobalTheory_SA_TransvG_det_fromBlocks_swap
import Theorems.Thm_GlobalTheory_SA_TransvG_det_updateRow_last
import Theorems.Thm_GlobalTheory_SA_TransvG_det_fromBlocks_single
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix
open GlobalTheory GlobalTheory.SA GlobalTheory.SA.TransvG
variable {K : Type} [CommRing K]
namespace GlobalTheory.SA.TransvG
theorem _root_.solution {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) A B
      (diagonal fun a => if a = Fin.last r then -T' else 0)).det =
      (-1) ^ (r + 1) * (A.det * B.det - T * T' *
        ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have h : (-diagonal fun a => if a = Fin.last r then -T' else 0) =
      diagonal fun a => if a = Fin.last r then T' else 0 := by
    ext a b
    simp only [Matrix.neg_apply, diagonal_apply]
    split_ifs <;> simp
  have h2 : (-A).submatrix Fin.castSucc Fin.castSucc = -A.submatrix Fin.castSucc Fin.castSucc := rfl
  rw [det_fromBlocks_swap, h, det_fromBlocks_single, det_updateRow_last, det_updateRow_last, h2, det_neg, det_neg]
  simp only [Fintype.card_fin]
  ring
end GlobalTheory.SA.TransvG
