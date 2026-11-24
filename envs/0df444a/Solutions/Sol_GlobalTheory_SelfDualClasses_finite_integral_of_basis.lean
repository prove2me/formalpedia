-- Prove2me | solution 1 for GlobalTheory.SelfDualClasses.finite_integral_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:14.03291+00:00
-- url     : https://prove2.me/submissions/c555a2a0-5b67-4442-a0f7-4b016e4ce3ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_nondegenerate


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
open GlobalTheory.SelfDualClasses
open ShortVectors
namespace GlobalTheory.SelfDualClasses
theorem _root_.solution {n : ℕ} {ι : Type} [Fintype ι] (b : Basis ι ℚ (Fin n → E)) :
    {Λ : Submodule (𝓞 E) (Fin n → E) | (∀ i, b i ∈ Λ) ∧
      ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)}.Finite := by
  classical
  let L₀ : Submodule ℤ (Fin n → E) := span ℤ (Set.range b)
  let L₁ : Submodule ℤ (Fin n → E) := (traceHerm n).dualSubmodule L₀
  have hfg : L₁.FG := by
    simp only [L₁, L₀]
    rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ (traceHerm_nondegenerate n)]
    exact fg_span (Set.finite_range _)
  have : Module.Finite ℤ L₁ := Module.Finite.iff_fg.mpr hfg
  have : Finite (L₁ ⧸ L₀.submoduleOf L₁) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : (x : Fin n → E) ∈ span ℚ (Set.range b) := b.mem_span _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ _ _ hx
    refine ⟨t, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ht
  have h0 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) → ∀ x ∈ L₀, x ∈ Λ := by
    intro Λ hΛ
    have : L₀ ≤ Λ.restrictScalars ℤ := span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact this
  have h1 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → ∀ x ∈ Λ, x ∈ L₁ := by
    intro Λ hΛ hint x hx y hy
    have := Algebra.isIntegral_trace (L := ℚ) (hint x hx y (h0 Λ hΛ y hy))
    rw [Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp this
  let F : Submodule (𝓞 E) (Fin n → E) → Set (L₁ ⧸ L₀.submoduleOf L₁) :=
    fun Λ => {q | ∃ x : L₁, (x : Fin n → E) ∈ Λ ∧ Submodule.Quotient.mk x = q}
  have key : ∀ Λ Λ' : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ i, b i ∈ Λ') → F Λ = F Λ' → Λ ≤ Λ' := by
    intro Λ Λ' hΛ hint hΛ' hF x hx
    have : Submodule.Quotient.mk ⟨x, h1 Λ hΛ hint x hx⟩ ∈ F Λ := ⟨_, hx, rfl⟩
    rw [hF] at this
    obtain ⟨y, hy, hq⟩ := this
    rw [Submodule.Quotient.eq] at hq
    have h2 : (y : Fin n → E) - x ∈ Λ' := h0 Λ' hΛ' _ hq
    simpa using Λ'.sub_mem hy h2
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro Λ ⟨hΛ, hi⟩ Λ' ⟨hΛ', hi'⟩ hF
  exact le_antisymm (key _ _ hΛ hi hΛ' hF) (key _ _ hΛ' hi' hΛ hF.symm)
end GlobalTheory.SelfDualClasses
