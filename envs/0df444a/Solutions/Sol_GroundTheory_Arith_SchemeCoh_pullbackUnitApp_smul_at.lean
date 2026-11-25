-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:51.670823+00:00
-- url     : https://prove2.me/submissions/75c76bd5-0882-4489-a428-241c94827ed3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange

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
variable {W T U : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (g : T ⟶ U) (N : U.Modules) (O : U.Opens) (a : Γ(U, O))
    (n : Γ(N, O)) :
    Etale.pullbackUnitApp g N O (a • n) = g.app O a • Etale.pullbackUnitApp g N O n :=
  Scheme.Modules.Hom.app_smul _ a n
end GroundTheory.Arith.SchemeCoh
