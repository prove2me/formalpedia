-- Prove2me | solution 1 for GlobalTheory.SA.FlagExample.isPairMap_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:41.701242+00:00
-- url     : https://prove2.me/submissions/a82053c3-71b2-4d44-a97e-6d3165269698

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_gL_eq_smulLat
import Theorems.Thm_GlobalTheory_SA_isPairMap_of_aut
import Theorems.Thm_GlobalTheory_SA_FlagExample_mem_lat
import Theorems.Thm_GlobalTheory_SA_FlagExample_isCong_fl
import Theorems.Thm_GlobalTheory_SA_FlagExample_co_flip
import Theorems.Thm_GlobalTheory_SA_FlagExample_flip_vec
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
import Theorems.Thm_GlobalTheory_SA_mem_gL
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
theorem _root_.solution :
    IsPairMap (flZero E) (flPos E) (flNeg E) (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) (flip E) := by
  have hL : ∀ x, flip E x ∈ (wittSpace E 2 1).L0 ↔ x ∈ (wittSpace E 2 1).L0 := fun x => by
    rw [mem_lat, mem_lat]
    refine forall_congr' fun i => ?_
    rw [co_flip]
    split_ifs
    · exact neg_mem_iff (H := (algebraMap (𝓞 E) E).range)
    · rfl
  refine isPairMap_of_aut (isCong_fl E _ _) ((mem_isomGrp _ _).2 fun x y => ?_) ?_ ?_ ?_ fun l hl => ?_
  · rw [sp_B, sp_B]; simp [co_flip]
  · ext y
    obtain ⟨x, rfl⟩ := (flip E).surjective y
    rw [mem_imLat]
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ (hL y).2 hy, fun hx => ⟨x, (hL x).1 hx, rfl⟩⟩
  · rw [fl_X, fl_X, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, flip_vec]; rfl
  · have e : flip E (flPos E).z = (flNeg E).z := flip_vec E _ _ _ _ _
    rw [e, sub_self]
    exact zero_mem _
  · refine Submodule.mem_sup_right ?_
    rw [← gL_eq_smulLat, mem_gL]
    refine ⟨(fun i => if i = 3 then -co E l i else 0 : Fin 5 → E), (mem_lat E _).2 fun i => ?_,
      funext fun i : Fin 5 => ?_⟩
    · show (if i = 3 then -co E l i else 0) ∈ (algebraMap (𝓞 E) E).range
      split_ifs
      · exact neg_mem ((mem_lat E l).1 hl.1 i)
      · exact zero_mem _
    · show ((2 : ℕ) : E) * (if i = 3 then -co E l i else 0) = co E (flip E l) i - co E l i
      rw [co_flip]
      split_ifs <;> push_cast <;> ring
end GlobalTheory.SA.FlagExample
