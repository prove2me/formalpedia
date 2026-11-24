-- Prove2me | solution 1 for GlobalTheory.root_of_unity_eq_one_of_conj_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:42.843314+00:00
-- url     : https://prove2.me/submissions/5b619f74-fe45-44af-a85d-8f4d60c38f08

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RootOfUnityEqOneOfConjCongruence
import Theorems.Thm_GlobalTheory_isIntegral_eigenvalue_sub_one_div
import Theorems.Thm_GlobalTheory_root_of_unity_eq_one_of_isIntegral_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by
  intro E _ _ r M n Λ Λ' γ δ u τ Q hr hM hn hu hfg hfg' hsp hsp' hγ hδ hQ hconj
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (γ.map τ)ᵀ)
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hw1 : w ᵥ* γ.map τ = l • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply, Matrix.mulVec_transpose] at this
  have hwQ : w ᵥ* Q ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_vecMul_eq_zero hQ h)
  have hs : (u • γ).map τ = τ u • γ.map τ := by
    ext i j; simp
  have hw2 : (w ᵥ* Q) ᵥ* δ.map τ = (τ u * l) • (w ᵥ* Q) := by
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hs, Matrix.vecMul_smul, hw1,
      smul_smul, Matrix.smul_vecMul]
  have ha := isIntegral_eigenvalue_sub_one_div Λ γ τ hM0 hfg hsp hγ w hw0 l hw1
  have hb := isIntegral_eigenvalue_sub_one_div Λ' δ τ hM0 hfg' hsp' hδ _ hwQ _ hw2
  have hui : IsIntegral ℤ (τ u) := by
    apply IsIntegral.of_pow hn
    rw [← map_pow, hu, map_one]
    exact isIntegral_one
  have hc : τ ((u - 1) / M) = (τ u * l - 1) / M - τ u * ((l - 1) / M) := by
    rw [map_div₀, map_sub, map_one, map_natCast]
    field_simp
    ring
  refine root_of_unity_eq_one_of_isIntegral_div hM hn hu ?_
  refine (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 ?_
  change IsIntegral ℤ (τ ((u - 1) / M))
  rw [hc]
  exact hb.sub (hui.mul ha)
end GlobalTheory
