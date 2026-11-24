-- Prove2me | solution 1 for GlobalTheory.ExponentTrace.entry_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:15:37.306315+00:00
-- url     : https://prove2.me/submissions/543c94a2-cd86-482a-b872-d926c1b9508c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmFieldHostElementAddConjEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CuspPairingIntIffHermitianExponentIntegral
import Theorems.Thm_GlobalTheory_ExponentTrace_mem_mul_inv_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_trace_dual_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_ccc
import Theorems.Thm_GlobalTheory_coe_different_ne_zero
import Theorems.Thm_GlobalTheory_conjFrac_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.ExponentTrace
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.ExponentTrace
theorem _root_.solution (N : ℕ) (A : FractionalIdeal (𝓞 E)⁰ E) {B : FractionalIdeal (𝓞 E)⁰ E}
    (hB : B ≠ 0) (s : E) :
    (∀ y : E, (∀ a' ∈ B, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ A, s * y = (N : E) * z) ↔ s ∈ pairIdeal N A B := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have h0 : (dif E)⁻¹ * (conjFrac B)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hB')
  have e : pairIdeal N A B = (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A) *
      ((dif E)⁻¹ * (conjFrac B)⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv]; rfl
  rw [e, mem_mul_inv_iff h0]
  refine forall_congr' fun y => imp_congr ?_ FractionalIdeal.mem_singleton_mul.symm
  rw [← trace_dual_iff hB']
  constructor
  · intro h a ha
    have := h _ (mem_conjFrac.1 ha)
    rwa [ccc] at this
  · intro h a ha
    exact h _ (cc_mem_conjFrac.2 ha)
end GlobalTheory.ExponentTrace
