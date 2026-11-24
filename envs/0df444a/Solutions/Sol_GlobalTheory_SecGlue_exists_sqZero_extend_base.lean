-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_sqZero_extend_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:20.961622+00:00
-- url     : https://prove2.me/submissions/949fc6b2-7ede-46f1-bd33-2ed90053d261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
import Theorems.Thm_GlobalTheory_SecGlue_sqZeroInterp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SecGlue.sqZeroInterp_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S]
    [Algebra R' A] [Algebra R' S]
    [hfp : Algebra.FinitePresentation R' A] (J : Ideal S) (hJ : J ^ 2 = ⊥) (g : S)
    (φ : A →ₐ[R'] S) (ψ : A →ₐ[R'] Localization.Away g)
    (hψ : ∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈
      J.map (algebraMap S (Localization.Away g))) :
    ∃ N₀ : ℕ, ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N₀ *
          (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  obtain ⟨n, π, hπ, hker⟩ := hfp.out
  have hJg : (J.map (algebraMap S (Localization.Away g))) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hy : ∀ i : Fin n, ∃ k : ℕ, ∃ y ∈ J, algebraMap S (Localization.Away g) y =
      algebraMap S (Localization.Away g) g ^ k * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    obtain ⟨⟨⟨j, hj⟩, ⟨m, ⟨k, rfl⟩⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g)).1 (hψ (π (MvPolynomial.X i)))
    refine ⟨k, j, hj, ?_⟩
    simp only [map_pow] at e
    rw [← e]; ring
  choose k y hyJ hyeq using hy
  set M := Finset.univ.sup k with hM
  set y' : Fin n → S := fun i => g ^ (M - k i) * y i with hy'
  have hy'J : ∀ i, y' i ∈ J := fun i => J.mul_mem_left _ (hyJ i)
  have hy'eq : ∀ i, algebraMap S (Localization.Away g) (y' i) =
      algebraMap S (Localization.Away g) g ^ M * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    have hk : k i ≤ M := Finset.le_sup (Finset.mem_univ i)
    simp only [y', map_mul, map_pow, hyeq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set α₀ : MvPolynomial (Fin n) R' →ₐ[R'] S := φ.comp π with hα₀
  set β₀ : MvPolynomial (Fin n) R' →ₐ[R'] S :=
    MvPolynomial.aeval (fun i => φ (π (MvPolynomial.X i)) + y' i) with hβ₀
  have hβα : ∀ p, β₀ p - α₀ p ∈ J := by
    intro p
    rw [← Ideal.Quotient.eq]
    have e : (Ideal.Quotient.mkₐ R' J).comp β₀ = (Ideal.Quotient.mkₐ R' J).comp α₀ := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀, α₀, MvPolynomial.aeval_X]
      rw [Ideal.Quotient.eq]; simpa using hy'J i
    exact DFunLike.congr_fun e p
  have hloc : ∀ p, algebraMap S (Localization.Away g) (β₀ p) =
      algebraMap S (Localization.Away g) (α₀ p) + algebraMap S (Localization.Away g) g ^ M *
        (ψ (π p) - algebraMap S (Localization.Away g) (α₀ p)) := by
    intro p
    have e : (IsScalarTower.toAlgHom R' S (Localization.Away g)).comp β₀ =
        sqZeroInterp _ hJg ((IsScalarTower.toAlgHom R' S (Localization.Away g)).comp α₀)
          (ψ.comp π) (fun q => hψ (π q)) (algebraMap S (Localization.Away g) g ^ M) := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, sqZeroInterp_apply, IsScalarTower.coe_toAlgHom', β₀, α₀,
        MvPolynomial.aeval_X, map_add, hy'eq]
      rfl
    exact DFunLike.congr_fun e p

  obtain ⟨s, hs⟩ := hker
  have hrel : ∀ r ∈ s, ∃ K : ℕ, g ^ K * (β₀ r - α₀ r) = 0 := by
    intro r hr
    have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hπr : π r = 0 := hrk
    have hz : algebraMap S (Localization.Away g) (β₀ r - α₀ r) = 0 := by
      rw [map_sub, hloc]; simp [α₀, hπr]
    obtain ⟨⟨m, ⟨K, rfl⟩⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 hz
    exact ⟨K, hm⟩
  choose! Kf hKf using hrel
  set K := s.sup Kf with hK
  set θ := sqZeroInterp J hJ α₀ β₀ hβα (g ^ K) with hθ
  have hθker : ∀ r ∈ RingHom.ker π.toRingHom, θ r = 0 := by
    intro r hr
    rw [← hs] at hr
    have hle : Ideal.span (s : Set (MvPolynomial (Fin n) R')) ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro r hr
      have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
      have hπr : π r = 0 := hrk
      have hle' : Kf r ≤ K := Finset.le_sup hr
      show θ r = 0
      rw [hθ, sqZeroInterp_apply]
      have : α₀ r = 0 := by simp [α₀, hπr]
      have h2 := hKf r hr
      rw [this, sub_zero] at h2
      rw [this, sub_zero, zero_add, ← Nat.sub_add_cancel hle', pow_add, mul_assoc, h2, mul_zero]
    exact hle hr
  let χ₀ : A →ₐ[R'] S := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) θ hθker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hχ₀ : ∀ p, χ₀ (π p) = θ p := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ _ θ hθker ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = θ p
    rw [this]
    rfl
  refine ⟨K + M, χ₀, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, add_sub_cancel_left]
    exact J.mul_mem_left _ (hβα p)
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, map_add, map_mul, map_sub, hloc, map_pow, pow_add]
    ring
end GlobalTheory.SecGlue
