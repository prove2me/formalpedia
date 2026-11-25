-- Prove2me | solution 1 for GlobalTheory.IntPair.IsScalar.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:54.845887+00:00
-- url     : https://prove2.me/submissions/1b57b9dd-e9d0-43a5-be7f-3b67407d2f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
import Theorems.Thm_GlobalTheory_IntPair_corank_congr
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_SA_IsComp_congr
import Theorems.Thm_GlobalTheory_SA_IsPairMap_congr
import Theorems.Thm_GlobalTheory_SA_IsSig_congr
import Theorems.Thm_GlobalTheory_SA_X_le_xPlus
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
open GlobalTheory GlobalTheory.IntPair
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}
variable [FiniteDimensional K V]
omit [FiniteDimensional K V]
namespace GlobalTheory.IntPair
namespace IsScalar
theorem _root_.solution (h : IsScalar F F' F'' β) (e : SameRed F' F'' β β₁) : IsScalar F F' F'' β₁ :=
  ⟨h.1, h.2.1, (corank_congr e).trans h.2.2.1, fun y y' a a' k =>
    (h.2.2.2 y y' a a' k).congr (by simp) (e _ (perp_anti (X_le_xPlus F') k.2.1.2))⟩
end IsScalar
end GlobalTheory.IntPair
