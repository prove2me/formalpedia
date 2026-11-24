-- Prove2me | solution 1 for GlobalTheory.hermDual_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:55.844309+00:00
-- url     : https://prove2.me/submissions/fe149276-d973-4e9c-8c88-3b6883b05334

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
theorem _root_.solution :
    hermDual G Λ = Λ ↔ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → x ∈ Λ :=
  ⟨fun h => ⟨fun _ hx => (h.ge hx :), fun _ hx => h.le hx⟩, fun h => le_antisymm h.2 h.1⟩
end GlobalTheory
