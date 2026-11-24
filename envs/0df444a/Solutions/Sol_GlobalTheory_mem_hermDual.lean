-- Prove2me | solution 1 for GlobalTheory.mem_hermDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:26.593217+00:00
-- url     : https://prove2.me/submissions/68f1995b-9470-4937-aeaa-60a9816ed16f

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
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory
theorem _root_.solution {x : Fin r → E} :
    x ∈ hermDual G Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := Iff.rfl
end GlobalTheory
