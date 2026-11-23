-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.smul_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:44.536709+00:00
-- url     : https://prove2.me/submissions/69a5acfc-7294-4d02-a8c8-6274cbb14023

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L : Subgroup G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (σ : G) [(L.subgroupOf K).FiniteIndex]
    [((L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom)).FiniteIndex]
    (a : fixedModule A L) :
    σ • (norm A K L a : A) =
      norm A (K.map (MulAut.conj σ).toMonoidHom) (L.map (MulAut.conj σ).toMonoidHom)
        ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩ := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (K.map (MulAut.conj σ).toMonoidHom ⧸
    (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom))
  rw [coe_norm, coe_norm, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_bij (fun t _ => cosetConj σ t) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t _ t' _ h
    induction t using QuotientGroup.induction_on with
    | H τ =>
    induction t' using QuotientGroup.induction_on with
    | H τ' =>
      rw [cosetConj_mk, cosetConj_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      obtain ⟨x, hx, hx'⟩ := h
      have : x = (τ : G)⁻¹ * τ' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv, mul_inv_rev, inv_inv] at hx'
        have := congrArg (fun y => σ⁻¹ * y * σ) hx'
        simpa [mul_assoc] using this
      simpa [this] using hx
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H ρ =>
      obtain ⟨κ, hκ, hκρ⟩ := Subgroup.mem_map.1 ρ.2
      refine ⟨((⟨κ, hκ⟩ : K) : K ⧸ L.subgroupOf K), Finset.mem_univ _, ?_⟩
      rw [cosetConj_mk]
      congr 1
      ext
      simpa using hκρ
  · intro t _
    induction t using QuotientGroup.induction_on with
    | H τ =>
      rw [cosetConj_mk, cosetSMul_mk, cosetSMul_mk, smul_smul, smul_smul]
      simp
end GroundTheory.LocalField.Abstract
