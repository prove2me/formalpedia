-- Prove2me | solution 1 for GlobalTheory.conjFrac_different
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:06.635204+00:00
-- url     : https://prove2.me/submissions/40e85aa6-1f65-4853-9dd6-557312a64a5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_trace_cc
import Theorems.Thm_GlobalTheory_conjFrac_inv
import Theorems.Thm_GlobalTheory_mem_inv_different_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul



set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution :
    conjFrac ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) := by
  apply inv_injective
  rw [← conjFrac_inv]
  ext x
  rw [mem_conjFrac, mem_inv_different_iff, mem_inv_different_iff]
  constructor
  · intro h a ha
    rw [← trace_cc, cc_mul]
    exact h _ (isIntegral_cc ha)
  · intro h a ha
    rw [← trace_cc, cc_mul, cc_cc]
    exact h _ (isIntegral_cc ha)
end GlobalTheory
