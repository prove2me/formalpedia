-- Prove2me | solution 1 for GlobalTheory.SA.IsPairMap.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:21.97849+00:00
-- url     : https://prove2.me/submissions/ded7f2dc-0ea6-4db8-bd71-4e900f089ab1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_z_mem_perp
import Theorems.Thm_GlobalTheory_SA_B_congr
import Theorems.Thm_GlobalTheory_SA_mem_redLat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
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
variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}
namespace GlobalTheory.SA
namespace IsPairMap
theorem _root_.solution (h : IsPairMap F F' F'' Λ g β) {β₁ : V ≃ₗ[K] V}
    (h1 : F'.X.map (β₁ : V →ₗ[K] V) = F''.X) (h2 : (perp H F'.X).map (β₁ : V →ₗ[K] V) = perp H F''.X)
    (he : ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X) : IsPairMap F F' F'' Λ g β₁ := by
  have k2 : ∀ x, β₁ x ∈ perp H F''.X ↔ x ∈ perp H F'.X := fun x => by rw [← h2]; simp
  refine isPairMap_of_mem_iff (fun x => by rw [← h1]; simp) k2 (fun x hx y hy => ?_) (fun x => ?_) ?_
    fun l hl l' hl' e => h.2.2.2.2.2 l hl l' hl' ?_
  · rw [B_congr F'' ((h.mem_perp_iff x).2 hx) ((h.mem_perp_iff y).2 hy) (he x hx) (he y hy), h.2.2.1 x hx y hy]
  · have k : x ∈ perp H F'.X → (β₁ x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ) := fun hx => by
      have hm : β₁ x - β x ∈ redLat F'' Λ := Submodule.mem_sup_right (he x hx)
      rw [← h.mem_redLat_iff, ← Submodule.add_mem_iff_right _ hm (y := β x), sub_add_cancel]
    exact ⟨fun hx => (k ((k2 x).1 ((mem_redLat _ _ _).1 hx).1)).1 hx,
      fun hx => (k ((mem_redLat _ _ _).1 hx).1).2 hx⟩
  · simpa using add_mem (he _ (z_mem_perp F')) h.2.2.2.2.1
  · simpa using sub_mem e (he l hl.2)
end IsPairMap
end GlobalTheory.SA
