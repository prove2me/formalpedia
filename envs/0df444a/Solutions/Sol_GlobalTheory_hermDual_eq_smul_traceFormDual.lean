-- Prove2me | solution 1 for GlobalTheory.hermDual_eq_smul_traceFormDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:56.719891+00:00
-- url     : https://prove2.me/submissions/489c5a0c-d3dd-4b40-a427-4d08b2226805

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_coe_different_ne_zero
import Theorems.Thm_GlobalTheory_fractionalIdeal_smul_inv_smul
import Theorems.Thm_GlobalTheory_traceFormDual_eq

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
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory
theorem _root_.solution {ξ : E} (hξ : ξ ≠ 0) :
    hermDual G Λ =
      ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • traceFormDual ξ G Λ := by
  rw [traceFormDual_eq hξ, fractionalIdeal_smul_inv_smul
    (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ) coe_different_ne_zero)]
end GlobalTheory
