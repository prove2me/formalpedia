-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:34.443804+00:00
-- url     : https://prove2.me/submissions/1f800b37-1795-46fa-bb99-5e42cf24afcc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
open GroundTheory.Arith.SchemeCoh.Scheme GroundTheory.Arith.SchemeCoh.Scheme.Modules GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn
namespace GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn
theorem _root_.solution {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' :=
  fun U hU s => h U (hU.mono_right hT) s
end GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn
