-- Prove2me | solution 1 for GlobalTheory.SA.TransvG.det_fromBlocks_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:43.580328+00:00
-- url     : https://prove2.me/submissions/c5cfa8f3-8504-4ddf-8c2f-6afc292eb711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_SA_IsComp_swap
import Theorems.Thm_GlobalTheory_SA_IsSig_swap
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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (l : n) (X Y : Matrix n n K) (t s : K) :
    (fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y).det =
      X.det * Y.det - t * s * ((X.updateRow l (Pi.single l 1)).det * (Y.updateRow l (Pi.single l 1)).det) := by
  have e1 : fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y =
      (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y (Sum.inl l) +
          t • Pi.single (Sum.inr l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e2 : (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (Pi.single (Sum.inr l) 1) =
      (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y (Sum.inr l) +
          s • Pi.single (Sum.inl l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e3 : (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1) =
      (fromBlocks (X.updateRow l (Pi.single l 1)) 0 0 (Y.updateRow l (Pi.single l 1))).submatrix
        (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb, @eq_comm _ l b]
  have e4 : (X.updateRow l 0).det = 0 := det_eq_zero_of_row_eq_zero l fun j => by simp
  rw [e1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₁₂, e2,
    det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₂₁, e3, det_permute,
    det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), e4]
  simp
  ring
end GlobalTheory.SA.TransvG
