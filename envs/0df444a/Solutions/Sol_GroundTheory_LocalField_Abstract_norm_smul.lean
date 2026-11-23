-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.norm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:44.298181+00:00
-- url     : https://prove2.me/submissions/883b9318-10da-454d-a3d2-4b23a81a20b1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
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
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)
variable {A K L}
variable (A K L)
variable [(L.subgroupOf K).FiniteIndex]
variable {A K L}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution [(L.subgroupOf K).Normal] (g : K) (a : fixedModule A L)
    (hga : (g : G) • (a : A) ∈ fixedModule A L) :
    norm A K L ⟨(g : G) • (a : A), hga⟩ = norm A K L a := by
  ext
  rw [coe_norm, coe_norm]
  have h : ∀ q : K ⧸ L.subgroupOf K,
      cosetSMul A K L ⟨(g : G) • (a : A), hga⟩ q = cosetSMul A K L a (q * (g : K ⧸ L.subgroupOf K)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [← QuotientGroup.mk_mul, cosetSMul_mk, cosetSMul_mk]
      simp [smul_smul]
  simp_rw [h]
  exact finprod_comp_equiv (Equiv.mulRight _)
end GroundTheory.LocalField.Abstract
