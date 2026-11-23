-- Prove2me | solution 1 for GlobalTheory.ShortVectors.traceHerm_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:23.193791+00:00
-- url     : https://prove2.me/submissions/beee5f77-e668-4ea6-a5ec-1be2831e4a84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_apply
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_symm
import Theorems.Thm_GlobalTheory_TraceDualMin_trace_cc


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
theorem _root_.solution (n : ℕ) : (traceHerm (E := E) n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [traceHerm_apply, traceHerm_apply, DualFamily.herm_one_symm x y, TraceDualMin.trace_cc]
end GlobalTheory.ShortVectors
