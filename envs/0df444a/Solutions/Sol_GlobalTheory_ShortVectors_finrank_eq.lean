-- Prove2me | solution 1 for GlobalTheory.ShortVectors.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:48.176645+00:00
-- url     : https://prove2.me/submissions/62f1b144-3faa-456f-b3a4-e563545dea17

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
theorem _root_.solution : finrank ℚ E = 2 * fdeg E := by
  rw [fdeg, NumberField.IsTotallyComplex.finrank]
  omega
end GlobalTheory.ShortVectors
