-- Prove2me | solution 1 for GlobalTheory.fractionalIdeal_inv_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:59.701395+00:00
-- url     : https://prove2.me/submissions/9b87967f-77bb-4a50-9aa1-416d7d607586

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
    ((a⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • (a : Submodule (𝓞 E) E) • Λ = Λ := by
  rw [← fractionalIdeal_mul_smul, inv_mul_cancel₀ ha, fractionalIdeal_one_smul]
end GlobalTheory
