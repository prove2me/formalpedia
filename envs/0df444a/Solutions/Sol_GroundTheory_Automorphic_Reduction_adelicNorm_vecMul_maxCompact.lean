-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adelicNorm_vecMul_maxCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:06.628187+00:00
-- url     : https://prove2.me/submissions/ad618e25-11e7-4064-b3fa-c40b1b4d3b42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_vecMul_GL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_vecMul_GL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_integralGL


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
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (y : Fin n → 𝔸[K]) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) :
    adelicNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])) = adelicNorm y := by
  rw [adelicNorm, adelicNorm]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [infComp_vecMul_GL, hk.1 w]
  · refine finprod_congr fun v => ?_
    rw [finComp_vecMul_GL, norm_vecMul_integralGL v (hk.2 v)]
end GroundTheory.Automorphic.Reduction
