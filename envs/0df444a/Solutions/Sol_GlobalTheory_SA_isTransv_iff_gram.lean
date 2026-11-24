-- Prove2me | solution 1 for GlobalTheory.SA.isTransv_iff_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:11.736261+00:00
-- url     : https://prove2.me/submissions/cf23cd7a-8bb6-4394-ac45-cf80081c7159

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
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
namespace GlobalTheory.SA
theorem _root_.solution (F F' : FlagD H r) : IsTransv F F' ↔ (Gram F F').det ≠ 0 := by
  classical
  have hV : V0 F F' = Submodule.span K (Set.range (Sum.elim F.e F'.e)) := by
    rw [Set.Sum.elim_range, Submodule.span_union, ← xPlus_eq_span, ← xPlus_eq_span, xPlus_sup]
  have hW : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → K,
      ∑ p, c p • Sum.elim F.e F'.e p ∈ wSp F F' ↔ Matrix.vecMul c (Gram F F') = 0 := fun c => by
    rw [wSp, hV, mem_perp_span, Set.forall_mem_range, funext_iff]
    refine forall_congr' fun q => ?_
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Gram, Matrix.of_apply,
      Pi.zero_apply]
  have hcard : Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 := by simp; omega
  have hli : LinearIndependent K (Sum.elim F.e F'.e) ↔ Module.finrank K (V0 F F') = 2 * r + 2 := by
    rw [linearIndependent_iff_card_eq_finrank_span, hV, hcard, eq_comm]; rfl
  rw [IsTransv, ← hli, Fintype.linearIndependent_iff, Ne, ← Matrix.exists_vecMul_eq_zero_iff,
    Submodule.disjoint_def]
  constructor
  · rintro ⟨h1, h2⟩ ⟨c, hc, h0⟩
    refine hc (funext (h1 c (h2 _ ?_ ((hW c).2 h0))))
    rw [hV]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · intro h
    have k : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → K, ∑ p, c p • Sum.elim F.e F'.e p ∈ wSp F F' → c = 0 :=
      fun c hc => by_contra fun hne => h ⟨c, hne, (hW c).1 hc⟩
    refine ⟨fun c hc => congrFun (k c (hc ▸ zero_mem _)), fun x hx hw => ?_⟩
    rw [hV] at hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    simp [k c hw]
end GlobalTheory.SA
