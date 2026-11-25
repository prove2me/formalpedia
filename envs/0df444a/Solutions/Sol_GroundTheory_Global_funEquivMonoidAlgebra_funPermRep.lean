-- Prove2me | solution 1 for GroundTheory.Global.funEquivMonoidAlgebra_funPermRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:53.004607+00:00
-- url     : https://prove2.me/submissions/6d73ffea-e60e-42d9-9d51-92a434ff9281

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coeff_permOfFun



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]
variable {k G X}
namespace GroundTheory.Global
theorem _root_.solution [Finite X] (g : G) (F : X → ℤ) :
    funEquivMonoidAlgebra (funPermRep ℤ G X g F) =
      Representation.ofMulAction ℤ G X g (funEquivMonoidAlgebra F) := by
  ext x
  change (permOfFun _).coeff x = _
  rw [coeff_permOfFun, Representation.coeff_ofMulAction]
  change _ = (permOfFun F).coeff _
  rw [coeff_permOfFun, funPermRep_apply]
end GroundTheory.Global
