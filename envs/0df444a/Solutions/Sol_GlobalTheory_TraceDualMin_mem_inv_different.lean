-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.mem_inv_different
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:07.055796+00:00
-- url     : https://prove2.me/submissions/67593bec-1915-489c-ab51-02569b66d6db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Theorems.Thm_GlobalTheory_dual_one_eq_inv_differentIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.TraceDualMin
omit [IsCMField E]
namespace GlobalTheory.TraceDualMin
theorem _root_.solution {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one,
    Submodule.mem_traceDual]
  intro a ha
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨k, hk⟩ := hx b
  exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
end GlobalTheory.TraceDualMin
