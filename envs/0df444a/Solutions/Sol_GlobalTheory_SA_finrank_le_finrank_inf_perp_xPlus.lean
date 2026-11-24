-- Prove2me | solution 1 for GlobalTheory.SA.finrank_le_finrank_inf_perp_xPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:05.324861+00:00
-- url     : https://prove2.me/submissions/2b78f9a0-2ef0-40cd-966c-cc79a820448b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
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
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA
open GlobalTheory GlobalTheory.SA
namespace GlobalTheory.SA
theorem _root_.solution {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (S : Submodule K V) (F : FlagD H r) :
    Module.finrank K S ≤ Module.finrank K ↥(S ⊓ perp H (xPlus F)) + (r + 1) := by
  let f : S →ₗ[K] (Fin (r + 1) → K) := (LinearMap.pi fun i => H.B.flip (F.e i)).comp S.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank K (LinearMap.range f) ≤ r + 1 :=
    (Submodule.finrank_le _).trans (by simp)
  have h3 : (LinearMap.ker f).map S.subtype = S ⊓ perp H (xPlus F) := by
    ext y
    rw [Submodule.mem_inf, xPlus_eq_span, mem_perp_span, Set.forall_mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, LinearMap.mem_ker.2 (funext h), rfl⟩
  rw [← h3, Submodule.finrank_map_subtype_eq]
  omega
end GlobalTheory.SA
