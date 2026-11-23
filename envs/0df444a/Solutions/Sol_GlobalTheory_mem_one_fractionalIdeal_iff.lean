-- Prove2me | solution 1 for GlobalTheory.mem_one_fractionalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:22.595143+00:00
-- url     : https://prove2.me/submissions/505f6273-da68-4172-99d5-f51fbe474c1e

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
omit [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {x : E} :
    x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩
end GlobalTheory
