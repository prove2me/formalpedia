-- Prove2me | solution 1 for GlobalTheory.mem_traceFormDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:59.441167+00:00
-- url     : https://prove2.me/submissions/a8a7bc84-3b55-47e0-b310-0a6d17aba1a2

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
theorem _root_.solution {ξ : E} {x : Fin r → E} :
    x ∈ traceFormDual ξ G Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k := Iff.rfl
end GlobalTheory
