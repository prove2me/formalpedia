-- Prove2me | solution 1 for GlobalTheory.GenericValue.exists_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:24:49.989795+00:00
-- url     : https://prove2.me/submissions/b9872c99-d5a2-4093-bb5a-d7f8dc435bcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GenericValue_exists_algHom_of_isTranscendenceBasis
import Theorems.Thm_GlobalTheory_GenericValue_mem_range_of_fixed
import Theorems.Thm_GlobalTheory_GenericValue_isTranscendenceBasis_genX
import Theorems.Thm_GlobalTheory_GenericValue_exists_generization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution [IsAlgClosed K] {I : Type}
    (V : ∀ (R : Type) [CommRing R] [Algebra K R], (I → R) → R → Prop)
    (bc : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (T : I → R) (a : R), V R T a → V R' (j ∘ T) (j a))
    (uniq : ∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a a' : F), V F T a → V F T a' → a = a')
    (ex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T : I → Ω), AlgebraicIndependent K T → ∃ a, V Ω T a)
    (gg : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K (Sum.elim T T') → V Ω T a → V Ω T' a' → a = a')
    (lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω) (T : I → O) (a : Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V Ω (r ∘ T) a →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
        (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧ V O' (j ∘ T) u) :
    ∃ κ : K, (∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a : F), V F T a → a = algebraMap K F κ) ∧
      V (Gen K I) (genX K I) (algebraMap K _ κ) := by
  have hA : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K T → AlgebraicIndependent K T' → V Ω T a → V Ω T' a' → a = a' := by
    intro Ω _ _ _ T T' a a' hT hT' h h'
    let j := IsScalarTower.toAlgHom K Ω (Gen Ω I)
    have hX := (isTranscendenceBasis_genX Ω I).1
    obtain ⟨b, hb⟩ := ex (Gen Ω I) _ (hX.restrictScalars (algebraMap K Ω).injective)
    have key : ∀ (S : I → Ω) (c : Ω), AlgebraicIndependent K S → V Ω S c → b = j c := fun S c hS hc =>
      gg (Gen Ω I) _ _ _ _ (hS.sumElim_comp hX) hb (bc Ω _ j S c hc)
    exact j.toRingHom.injective ((key T a hT h).symm.trans (key T' a' hT' h'))
  have hB := isTranscendenceBasis_genX K I
  obtain ⟨a₁, ha₁⟩ := ex (Gen K I) _ hB.1
  obtain ⟨κ, rfl⟩ := mem_range_of_fixed (K := K) a₁ fun j =>
    hA _ _ _ _ _ (hB.1.map' j.toRingHom.injective) hB.1 (bc _ _ j _ _ ha₁) ha₁
  refine ⟨κ, fun F _ _ T a h => ?_, ha₁⟩
  obtain ⟨O, _, _, _, _, Ω, _, _, _, r, e, S, hr, hS, hT⟩ := exists_generization (K := K) T
  have h₁ := bc _ _ e T a h
  rw [← hT] at h₁
  obtain ⟨O', _, _, _, _, j, r', u, hj, hr', hu⟩ := lift O Ω r S _ hr h₁
  have h₂ := bc _ _ r' _ _ hu
  rw [← Function.comp_assoc, ← AlgHom.coe_comp, hr'] at h₂
  have h₃ := uniq _ _ _ _ h₁ h₂
  let Ω' := AlgebraicClosure (FractionRing O')
  let i := IsScalarTower.toAlgHom K O' Ω'
  have hi : Function.Injective i := by
    show Function.Injective (algebraMap O' Ω')
    rw [IsScalarTower.algebraMap_eq _ (FractionRing O')]
    exact (algebraMap (FractionRing O') Ω').injective.comp (IsFractionRing.injective _ _)
  obtain ⟨m, hm⟩ := exists_algHom_of_isTranscendenceBasis hB ((hS.map' hj).map' hi)
  have h₄ := bc _ _ m _ _ ha₁
  rw [show m ∘ genX K I = i ∘ j ∘ S from funext hm] at h₄
  have h₅ : u = algebraMap K O' κ := hi ((uniq _ _ _ _ (bc _ _ i _ _ hu) h₄).trans (by simp))
  apply e.toRingHom.injective
  simpa [h₅] using h₃
end GlobalTheory.GenericValue
