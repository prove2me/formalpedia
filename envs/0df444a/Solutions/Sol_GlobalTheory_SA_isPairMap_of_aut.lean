-- Prove2me | solution 1 for GlobalTheory.SA.isPairMap_of_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:59.730088+00:00
-- url     : https://prove2.me/submissions/5afd0c75-fbb3-4551-8425-e7b84185b345

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_mem_redLat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
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
theorem _root_.solution (hc : IsCong F F'' Λ g) (hβ : β ∈ isomGrp H) (hΛ : imLat β Λ = Λ)
    (hX : F'.X.map (β : V →ₗ[K] V) = F''.X) (hz : β F'.z - F''.z ∈ F''.X)
    (hι : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), β l' - l' ∈ latX F Λ ⊔ smulLat g Λ) :
    IsPairMap F F' F'' Λ g β := by
  have hB := (mem_isomGrp H β).1 hβ
  have k0 : ∀ x, β x ∈ Λ ↔ x ∈ Λ := fun x => by
    conv_lhs => rw [← hΛ, mem_imLat]
    exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have k1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X := fun x => by rw [← hX]; simp
  have k2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := fun x => by
    rw [mem_perp_iff, mem_perp_iff, β.surjective.forall]
    simp only [k1, hB]
  refine isPairMap_of_mem_iff k1 k2 (fun x _ y _ => hB x y) (fun x => ?_) hz fun l hl l' hl' e => ?_
  · rw [mem_redLat, mem_redLat, k2, β.surjective.exists]
    simp only [k1, ← map_add, k0]
  · have h1 : β l - l' ∈ latX F Λ ⊔ smulLat g Λ :=
      hc.1 ▸ Submodule.mem_sup_left ⟨sub_mem ((k0 l).2 hl.1) hl'.1, e⟩
    simpa using sub_mem (hι l hl) h1
end GlobalTheory.SA
