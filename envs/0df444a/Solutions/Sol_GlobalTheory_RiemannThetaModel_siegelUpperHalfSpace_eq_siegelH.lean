-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.siegelUpperHalfSpace_eq_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:22.785958+00:00
-- url     : https://prove2.me/submissions/69f4d72e-8f76-45dd-97b2-e6446ccc6cbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_RiemannThetaModel_isSiegel_iff_mem_siegelH
import Theorems.Thm_GlobalTheory_isSiegel_iff_mem_siegelH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution :
    siegelUpperHalfSpace ι = ReciprocityTheory.PTheta.SiegelH ι :=
  Set.ext fun _ => mem_siegelUpperHalfSpace.trans isSiegel_iff_mem_siegelH
end GlobalTheory.RiemannThetaModel
