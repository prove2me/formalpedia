-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.prod_norm_mul_finprod_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:47.821125+00:00
-- url     : https://prove2.me/submissions/1a9afcf3-ae76-4c73-8bce-6cbc02ed1b73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_eq


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
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {c : K} (hc : c ≠ 0) :
    (∏ w : InfinitePlace K, ‖(c : w.Completion)‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(c : v.adicCompletion K)‖ = 1 := by
  have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (Units.mk0 c hc)
  rw [Subtype.ext_iff, GroundTheory.Global.IdeleGroup.ideleModule_eq] at h
  exact h
end GroundTheory.Automorphic.Reduction
