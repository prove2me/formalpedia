-- Prove2me | solution 1 for GlobalTheory.SelfDualClasses.hermRat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:15.938932+00:00
-- url     : https://prove2.me/submissions/123e70cd-a2b3-4d5c-bbd1-d51ff4671e27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.SelfDualClasses
open ShortVectors
namespace GlobalTheory.SelfDualClasses
theorem _root_.solution {n : ℕ} (x y : Fin n → E) : hermRat n x y = herm 1 x y := rfl
end GlobalTheory.SelfDualClasses
