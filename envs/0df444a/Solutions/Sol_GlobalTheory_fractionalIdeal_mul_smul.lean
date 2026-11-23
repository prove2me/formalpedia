-- Prove2me | solution 1 for GlobalTheory.fractionalIdeal_mul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.209665+00:00
-- url     : https://prove2.me/submissions/3dcd90cc-c03c-4fe5-a68b-1267b3396cc0

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
theorem _root_.solution (a b : FractionalIdeal (𝓞 E)⁰ E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((a * b : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ =
      (a : Submodule (𝓞 E) E) • (b : Submodule (𝓞 E) E) • Λ := by
  rw [FractionalIdeal.coe_mul]
  exact Submodule.smul_assoc _ _ _
end GlobalTheory
