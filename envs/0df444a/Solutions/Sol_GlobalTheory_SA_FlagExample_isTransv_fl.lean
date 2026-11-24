-- Prove2me | solution 1 for GlobalTheory.SA.FlagExample.isTransv_fl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:01.594826+00:00
-- url     : https://prove2.me/submissions/5780bd51-43be-46b6-8647-83283fa70d02

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_isTransv_iff_gram
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
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
open GlobalTheory.SA.FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)
namespace GlobalTheory.SA.FlagExample
theorem _root_.solution {s : ℤ} (h2 : s * s = 1) : IsTransv (flZero E) (fl E 1 s rfl h2) := by
  have h3 : (s : E) * s = 1 := by exact_mod_cast h2
  have hG : Gram (flZero E) (fl E 1 s rfl h2) =
      Matrix.fromBlocks !![0, 0; 0, -1] !![-2, 0; 0, -3] !![-2, 0; 0, -3] !![0, 0; 0, -1] := by
    ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;> refine (sp_B_vec E _ _).trans ?_ <;>
      simp <;> linear_combination 4 * h3
  rw [isTransv_iff_gram, hG, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  rintro ⟨c, hc, h⟩
  have a0 := congrFun h (Sum.inl 0)
  have a1 := congrFun h (Sum.inl 1)
  have b0 := congrFun h (Sum.inr 0)
  have b1 := congrFun h (Sum.inr 1)
  simp [Matrix.vecMul, dotProduct] at a0 a1 b0 b1
  have c1 : c (Sum.inr 1) = 0 := by linear_combination (1 / 8 : E) * b1 - (3 / 8 : E) * a1
  have c0 : c (Sum.inl 1) = 0 := by linear_combination (1 / 8 : E) * a1 - (3 / 8 : E) * b1
  refine hc (funext fun p => ?_)
  rcases p with p | p <;> fin_cases p <;> assumption
end GlobalTheory.SA.FlagExample
