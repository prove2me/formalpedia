-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.norm_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:30.671218+00:00
-- url     : https://prove2.me/submissions/5a22835a-f042-4e0b-bfc9-a45dccd55360

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L M : Subgroup G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] (a : fixedModule A M) :
    norm A K L (norm A L M a) = norm A K M a := by
  classical
  let _ := Fintype.ofFinite (K ⧸ M.subgroupOf K)
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (L ⧸ M.subgroupOf L)
  have hle : M.subgroupOf K ≤ L.subgroupOf K := fun x hx => hML hx
  ext
  simp only [coe_norm, finprod_eq_prod_of_fintype]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := Subgroup.quotientMapOfLE hle) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun p _ => ?_
  induction p using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
    refine Finset.prod_bij (fun t _ => cosetShift hLK σ t) ?_ ?_ ?_ ?_
    · intro t _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq]
        simp [Subgroup.mem_subgroupOf, mul_assoc]
    · intro t _ t' _ h
      induction t using QuotientGroup.induction_on with
      | H τ =>
      induction t' using QuotientGroup.induction_on with
      | H τ' =>
        rw [cosetShift_mk, cosetShift_mk, QuotientGroup.eq] at h
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
    · intro q hq
      rw [Finset.mem_filter] at hq
      induction q using QuotientGroup.induction_on with
      | H ρ =>
        have h := hq.2
        rw [Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq] at h
        have hmem : (σ : G)⁻¹ * ρ ∈ L := by
          have := L.inv_mem h
          simpa [Subgroup.mem_subgroupOf, mul_inv_rev] using this
        refine ⟨((⟨(σ : G)⁻¹ * ρ, hmem⟩ : L) : L ⧸ M.subgroupOf L), Finset.mem_univ _, ?_⟩
        rw [cosetShift_mk]
        congr 1
        ext
        simp
    · intro t _
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, cosetSMul_mk, cosetSMul_mk, smul_smul]
        rfl
end GroundTheory.LocalField.Abstract
