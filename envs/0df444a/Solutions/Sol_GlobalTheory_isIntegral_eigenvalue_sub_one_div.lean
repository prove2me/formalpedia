-- Prove2me | solution 1 for GlobalTheory.isIntegral_eigenvalue_sub_one_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:29.209982+00:00
-- url     : https://prove2.me/submissions/8784c90c-31f0-46e8-b8dd-7dc5835841ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RootOfUnityEqOneOfConjCongruence

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun x => w ⬝ᵥ (τ ∘ x)
      map_zero' := by simp [dotProduct]
      map_add' := fun x y => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ x, φ x = w ⬝ᵥ (τ ∘ x) := fun _ => rfl
  have hsm : ∀ (c : E) x, φ (c • x) = τ c * φ x := by
    intro c x
    simp only [hφ, dotProduct, Finset.mul_sum, Function.comp, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmul : ∀ x, φ (γ *ᵥ x) = l * φ x := by
    intro x
    have : τ ∘ (γ *ᵥ x) = γ.map τ *ᵥ (τ ∘ x) := funext fun i => RingHom.map_mulVec τ γ x i
    rw [hφ, this, Matrix.dotProduct_mulVec, hl, smul_dotProduct, hφ, smul_eq_mul]
  refine isIntegral_of_smul_mem_submodule
    ((Λ.restrictScalars ℤ).map φ.toIntLinearMap) ?_ (hfg.restrictScalars.map _) _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := by
      intro x hx
      have : φ.toIntLinearMap x ∈ (Λ.restrictScalars ℤ).map φ.toIntLinearMap :=
        Submodule.mem_map_of_mem hx
      rw [h0] at this
      simpa using this
    have h2 : ∀ x ∈ Submodule.span E (Λ : Set (Fin r → E)), φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [hsm, hx, mul_zero]
    apply hw
    funext i
    have h3 := h2 (Pi.single i 1) (hsp ▸ Submodule.mem_top)
    have h4 : τ ∘ (Pi.single i 1 : Fin r → E) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hφ, h4] at h3
    simpa using h3
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hγ x hx
    refine ⟨y, hy, ?_⟩
    have h := congrArg φ hxy
    rw [map_sub, hmul, hsm, map_natCast] at h
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    field_simp
    linear_combination -h
end GlobalTheory
