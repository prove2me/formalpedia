-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adelicGL_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:03.252603+00:00
-- url     : https://prove2.me/submissions/f6b31e6d-b29b-456f-ae53-51a33ef8358f

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
theorem _root_.solution {g h : AdelicGLn.AdelicGL K n} (h1 : ∀ w, infAt w g = infAt w h)
    (h2 : ∀ v, finAt v g = finAt v h) : g = h := by
  refine (AdelicGLn.restrictedProductEquiv K n).injective (Prod.ext (funext h1) ?_)
  exact RestrictedProduct.ext _ _ h2
end GroundTheory.Automorphic.Reduction
