-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.shortExact_tensorEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:14.625915+00:00
-- url     : https://prove2.me/submissions/5822075b-ca33-43c7-ae8a-34d75fe5b176

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (hL : IsInvertibleSheaf L) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (tensorEquivOfInvertible hL).functor).ShortExact :=
  hS.map_of_exact _
end GroundTheory.Arith.SchemeCoh
