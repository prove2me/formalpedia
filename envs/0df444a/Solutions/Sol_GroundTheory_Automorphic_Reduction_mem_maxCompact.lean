-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.mem_maxCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:49.404745+00:00
-- url     : https://prove2.me/submissions/5dccb0cf-9cb1-4fbd-bd7d-470fcb5d0a25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa

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
theorem _root_.solution {k : AdelicGLn.AdelicGL K n} :
    k ∈ maxCompact ↔ (∀ w, infAt w k ∈ archCompact w) ∧
      ∀ v, finAt v k ∈ GLnLocal.integralGL (v.adicCompletion K) n :=
  Iff.rfl
end GroundTheory.Automorphic.Reduction
