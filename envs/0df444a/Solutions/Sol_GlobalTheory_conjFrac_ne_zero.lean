-- Prove2me | solution 1 for GlobalTheory.conjFrac_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:33.396615+00:00
-- url     : https://prove2.me/submissions/65479d02-9428-4f1b-b635-c55266b71420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0) : conjFrac a ≠ 0 :=
  (map_ne_zero_iff _ conjFrac.injective).2 ha
end GlobalTheory
