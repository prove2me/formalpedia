-- Prove2me | solution 1 for GlobalTheory.mem_inv_different_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:43.412558+00:00
-- url     : https://prove2.me/submissions/c0526fdb-e884-4c92-8b2b-43ffc5d4ce66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_mem_one_fractionalIdeal_iff

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
    x ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔
      ∀ a : E, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv,
    FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
  refine forall_congr' fun a => ?_
  rw [mem_one_fractionalIdeal_iff, Algebra.traceForm_apply]
  exact imp_congr_right fun _ => ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
end GlobalTheory
