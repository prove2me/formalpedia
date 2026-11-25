-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:48.456662+00:00
-- url     : https://prove2.me/submissions/cbf6eaf2-70c2-453e-9591-6f8c7f22fcb3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
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
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K L : Subgroup G} (hKL : K ≤ L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) : (norm A K L a : A) = a := by
  have : Unique (K ⧸ L.subgroupOf K) :=
    { default := ((1 : K) : K ⧸ L.subgroupOf K)
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H σ =>
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact hKL (by simp) }
  rw [coe_norm, finprod_eq_single _ ((1 : K) : K ⧸ L.subgroupOf K)
    (fun q hq => absurd (Subsingleton.elim q _) hq), cosetSMul_mk]
  simp
end GroundTheory.LocalField.Abstract
