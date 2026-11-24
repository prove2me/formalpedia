-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.injectiveSequence_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:48.592839+00:00
-- url     : https://prove2.me/submissions/d99a7ef1-f140-424d-bf66-577629733e23

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived

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
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w' u
variable {X : TopCat.{u}} {B : Opens X → Prop}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (injectiveSequence F).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)))
    (inferInstanceAs (Mono (Injective.ι F))) coequalizer.π_epi
end GroundTheory.Arith.SchemeCoh
