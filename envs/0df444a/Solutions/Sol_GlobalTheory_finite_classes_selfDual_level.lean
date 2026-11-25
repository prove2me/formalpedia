-- Prove2me | solution 1 for GlobalTheory.finite_classes_selfDual_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:20:18.320423+00:00
-- url     : https://prove2.me/submissions/5365c902-6d6d-41c4-a46e-17c267257884

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_finite_classes_selfDual_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution (n N : ℕ) (hN : N ≠ 0) :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E),
      Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∀ f : Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}),
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  exact finite_classes_selfDual_pairs n _
end GlobalTheory
