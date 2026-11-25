-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.riemannThetaTerm_eq_thetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:19.50417+00:00
-- url     : https://prove2.me/submissions/dde37165-2db4-499f-9cfb-164faa1dd75f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic

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
theorem _root_.solution (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n = ReciprocityTheory.PTheta.thetaTerm a b v Ω n := rfl
end GlobalTheory.RiemannThetaModel
