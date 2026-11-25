-- Prove2me | solution 1 for GroundTheory.Global.divisorSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:06.797316+00:00
-- url     : https://prove2.me/submissions/d0113bd5-796c-4fff-b8e7-e0d1e954bc7b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum
import Theorems.Thm_GroundTheory_Global_mem_idealDivisors
import Theorems.Thm_GroundTheory_Global_idealDivisors_bot
import Theorems.Thm_GroundTheory_Global_divisorSum_bot
import Theorems.Thm_GroundTheory_Global_mul_sup_eq_of_le
import Theorems.Thm_GroundTheory_Global_sup_mul_sup_eq_of_le
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeffTerm_bot
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.coeffTerm_bot
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


attribute [local simp] GroundTheory.Global.idealDivisors_bot
attribute [local simp] GroundTheory.Global.divisorSum_bot

set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    {I J : Ideal (𝓞 K)} (hIJ : I ⊔ J = ⊤) : divisorSum ψ (I * J) = divisorSum ψ I * divisorSum ψ J := by
  by_cases hI : I = ⊥
  · simp [hI]
  by_cases hJ : J = ⊥
  · simp [hJ]
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI hJ
  rw [divisorSum, divisorSum, divisorSum, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun p _ ↦ p.1 * p.2) (fun D _ ↦ (D ⊔ I, D ⊔ J)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    rw [mem_idealDivisors hIJ0]
    exact Ideal.mul_mono hp.1 hp.2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ]
    exact ⟨le_sup_right, le_sup_right⟩
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    have h2 : p.1 * p.2 ⊔ J = p.2 := by
      rw [mul_comm]
      exact mul_sup_eq_of_le (by rwa [sup_comm]) hp.2 hp.1
    exact Prod.ext (mul_sup_eq_of_le hIJ hp.1 hp.2) h2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    exact sup_mul_sup_eq_of_le hIJ hD
  · intro p _
    exact (hψ p.1 p.2).symm
end GroundTheory.Global
