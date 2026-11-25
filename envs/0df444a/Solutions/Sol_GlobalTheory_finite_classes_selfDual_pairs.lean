-- Prove2me | solution 1 for GlobalTheory.finite_classes_selfDual_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:58:04.470444+00:00
-- url     : https://prove2.me/submissions/e8de86f5-f3b3-4fa0-a9a1-a57ac3fbcade

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_SelfDualClasses_finite_linearMap
import Theorems.Thm_GlobalTheory_finite_classes_selfDual_of_selfDual

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
theorem _root_.solution (n : ℕ) (T : Type) [AddCommGroup T] [Module (𝓞 E) T]
    [Finite T] :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ f : Λ →ₗ[𝓞 E] T,
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  classical
  obtain ⟨S, hS, hcl⟩ := finite_classes_selfDual_of_selfDual (E := E) n
  have hfin : {P : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T | P.1 ∈ S}.Finite := by
    refine (S.finite_toSet.biUnion (t := fun Λ => Set.range
      fun f : Λ →ₗ[𝓞 E] T => (⟨Λ, f⟩ : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T))
      fun Λ hΛ => ?_).subset ?_
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr (hS Λ hΛ).1
      have : Finite (Λ →ₗ[𝓞 E] T) := SelfDualClasses.finite_linearMap
      exact Set.finite_range _
    · rintro ⟨Λ, f⟩ h
      exact Set.mem_biUnion h ⟨f, rfl⟩
  refine ⟨hfin.toFinset, fun P hP => hS _ (hfin.mem_toFinset.mp hP), fun Λ h1 h2 h3 f => ?_⟩
  obtain ⟨Λ₀, hΛ₀, γ, hγ, h⟩ := hcl Λ h1 h2 h3
  exact ⟨⟨Λ₀, f ∘ₗ (γ.restrictScalars (𝓞 E)).toLinearMap.restrict fun x hx => (h x).mp hx⟩,
    hfin.mem_toFinset.mpr hΛ₀, γ, hγ, h, fun x => rfl⟩
end GlobalTheory
