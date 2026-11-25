-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.height_mul_maxCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:11.217338+00:00
-- url     : https://prove2.me/submissions/09f5cb10-8157-46e0-9e50-812e41847dca

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_vecMul_maxCompact

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
theorem _root_.solution (g : AdelicGLn.AdelicGL K n) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) (x : Fin n → K) : height (g * k) x = height g x := by
  rw [height, height, Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk]
end GroundTheory.Automorphic.Reduction
