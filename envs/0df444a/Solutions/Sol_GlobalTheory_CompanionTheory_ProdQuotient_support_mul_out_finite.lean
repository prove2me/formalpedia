-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:27.877107+00:00
-- url     : https://prove2.me/submissions/2c2ef34c-9c89-440a-84f8-7eb695b756bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdQuotient
namespace GlobalTheory.CompanionTheory.ProdQuotient
theorem _root_.solution (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  let φ : (G₁ × G₂) ⧸ K₁.prod K₂ → (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    fun q => ((q.out.1 : G₁ ⧸ K₁), (q.out.2 : G₂ ⧸ K₂))
  have hinj : Function.Injective φ := by
    intro a b hab
    have e₁ : ((a.out.1 : G₁ ⧸ K₁)) = (b.out.1 : G₁ ⧸ K₁) := congrArg Prod.fst hab
    have e₂ : ((a.out.2 : G₂ ⧸ K₂)) = (b.out.2 : G₂ ⧸ K₂) := congrArg Prod.snd hab
    rw [QuotientGroup.eq] at e₁ e₂
    have key : ((a.out : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂) = (b.out : G₁ × G₂) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.mpr ⟨e₁, e₂⟩
    simpa using key
  have inv₁ : ∀ g : G₁, f₁ (g : G₁ ⧸ K₁).out = f₁ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
    rw [hk]
    exact i₁ k k.2 g
  have inv₂ : ∀ g : G₂, f₂ (g : G₂ ⧸ K₂).out = f₂ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₂ g
    rw [hk]
    exact i₂ k k.2 g
  refine ((h₁.prod h₂).preimage hinj.injOn).subset ?_
  intro q hq
  have hq' : f₁ q.out.1 * f₂ q.out.2 ≠ 0 := hq
  refine ⟨?_, ?_⟩
  · change f₁ (q.out.1 : G₁ ⧸ K₁).out ≠ 0
    rw [inv₁]
    exact left_ne_zero_of_mul hq'
  · change f₂ (q.out.2 : G₂ ⧸ K₂).out ≠ 0
    rw [inv₂]
    exact right_ne_zero_of_mul hq'
end GlobalTheory.CompanionTheory.ProdQuotient
