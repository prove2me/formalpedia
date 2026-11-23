-- Prove2me | solution 1 for GlobalTheory.ShortVectors.traceHerm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:22.976123+00:00
-- url     : https://prove2.me/submissions/1da6ced9-be77-460d-baf0-5d2de6d7cced

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate

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
open GlobalTheory.ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ShortVectors
theorem _root_.solution {n : ℕ} (x y : Fin n → E) :
    traceHerm n x y = Algebra.trace ℚ E (herm 1 x y) := rfl
end GlobalTheory.ShortVectors
