-- Prove2me | solution 1 for GlobalTheory.fractionalIdeal_smul_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:45.380798+00:00
-- url     : https://prove2.me/submissions/2968129b-6336-4069-a8a7-fd2e5797f707

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_fractionalIdeal_mul_smul
import Theorems.Thm_GlobalTheory_fractionalIdeal_one_smul

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
theorem _root_.solution {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • ((a⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ = Λ := by
  rw [← fractionalIdeal_mul_smul, mul_inv_cancel₀ ha, fractionalIdeal_one_smul]
end GlobalTheory
