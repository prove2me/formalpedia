-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.index_eq_map_mul_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:06.055796+00:00
-- url     : https://prove2.me/submissions/cb0f8f2f-9d78-4f82-9ba1-b7680be2e991

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution {A B : Type} [Group A] [Group B] (φ : A →* B) (V : Subgroup A) :
    V.index = (V.map φ).relIndex φ.range * V.relIndex φ.ker := by
  have h1 : (V.map φ).relIndex φ.range = (V ⊔ φ.ker).index := by
    rw [← Subgroup.index_comap, Subgroup.comap_map_eq]
  have h2 : V.relIndex φ.ker = V.relIndex (V ⊔ φ.ker) := by
    refine Nat.card_congr (Equiv.ofBijective
      (Subgroup.quotientSubgroupOfEmbeddingOfLE V (le_sup_right : φ.ker ≤ V ⊔ φ.ker))
      ⟨Function.Embedding.injective _, ?_⟩)
    intro y
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective y
    have hg' : g ∈ ((φ.ker ⊔ V : Subgroup A) : Set A) := by rw [sup_comm]; exact hg
    rw [Subgroup.normal_mul] at hg'
    obtain ⟨a, ha, v, hv, rfl⟩ := hg'
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hv
  rw [h1, h2, mul_comm, Subgroup.relIndex_mul_index le_sup_left]
end GlobalTheory.SatakeWeyl.Heis
