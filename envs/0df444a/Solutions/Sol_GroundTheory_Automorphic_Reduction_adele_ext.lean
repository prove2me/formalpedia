-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adele_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:00.570693+00:00
-- url     : https://prove2.me/submissions/a3a72c01-d61a-4ac8-bad1-1215c6ace514

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
theorem _root_.solution {a b : 𝔸[K]} (h1 : ∀ w : InfinitePlace K, a.1 w = b.1 w)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), a.2 v = b.2 v) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)
end GroundTheory.Automorphic.Reduction
