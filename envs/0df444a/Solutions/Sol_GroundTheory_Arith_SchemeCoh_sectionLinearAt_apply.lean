-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:34.428703+00:00
-- url     : https://prove2.me/submissions/20662fa3-39bb-4f5e-bec7-fa66eb5e350c

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
theorem _root_.solution {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P')
    (O : X.Opens) (x : Γ(P, O)) : sectionLinearAt θ O x = θ.app O x := rfl
end GroundTheory.Arith.SchemeCoh
