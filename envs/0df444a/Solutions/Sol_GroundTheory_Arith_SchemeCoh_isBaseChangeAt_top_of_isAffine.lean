-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBaseChangeAt_top_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:36.317571+00:00
-- url     : https://prove2.me/submissions/2034f8cf-ed07-4518-8209-429590dbdaf5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_Etale_existsUnique_pullbackSection


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
theorem _root_.solution (h : T ⟶ U) [IsAffine T] [IsAffine U] (N : U.Modules)
    [N.IsQuasicoherent] : IsBaseChangeAt h N ⊤ := by
  intro Q _ instQ ψ hψ
  exact @Etale.existsUnique_pullbackSection T U h _ _ N _ Q _ instQ ψ hψ
end GroundTheory.Arith.SchemeCoh
