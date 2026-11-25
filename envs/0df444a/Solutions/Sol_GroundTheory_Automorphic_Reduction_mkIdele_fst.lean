-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.mkIdele_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:56.535044+00:00
-- url     : https://prove2.me/submissions/f040fff1-ee51-4e37-a981-0cf6a438c9ff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (w : InfinitePlace K) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).1 w = a w := by
  rw [← prodRestrictedEquiv_apply_fst, mkIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl
end GroundTheory.Automorphic.Reduction
