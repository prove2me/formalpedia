-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:34.531659+00:00
-- url     : https://prove2.me/submissions/d1839f33-6498-4e98-ae99-38de89de724e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_stalk_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
open AlgebraicGeometry CategoryTheory
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth f x
end GroundTheory.Arith.SchemeCoh
