-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finprod_le_finprod_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:54.667698+00:00
-- url     : https://prove2.me/submissions/8fb7e367-529e-4964-b136-b8be9007201e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {α : Type*} {f g : α → ℝ}
    (hf : (Function.mulSupport f).Finite) (hg : (Function.mulSupport g).Finite)
    (h0 : ∀ a, 0 ≤ f a) (h : ∀ a, f a ≤ g a) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 ha))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_right _ (hg.mem_toFinset.2 ha)))]
  exact Finset.prod_le_prod (fun a _ => h0 a) fun a _ => h a
end GroundTheory.Automorphic.Reduction
