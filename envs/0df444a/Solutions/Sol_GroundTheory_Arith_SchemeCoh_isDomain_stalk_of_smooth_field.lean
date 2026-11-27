-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:09.926106+00:00
-- url     : https://prove2.me/submissions/a08fca31-8a2a-4ef6-905c-882aa2557568

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_stalk_of_smooth_field
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain


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
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) :=
  have := isRegularLocalRing_stalk_of_smooth_field f x
  IsRegularLocalRing.isDomain
end GroundTheory.Arith.SchemeCoh
