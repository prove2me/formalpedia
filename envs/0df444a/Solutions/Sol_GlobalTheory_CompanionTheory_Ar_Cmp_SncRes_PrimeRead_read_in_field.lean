-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.read_in_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:21:14.305514+00:00
-- url     : https://prove2.me/submissions/bcc8826d-71d0-4153-8ee7-36eb85049342

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_aeval_eq_image
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_aeval_int_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_map_map_int
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_Kext_exists_algHom_adjoin_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
theorem _root_.solution {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω)
    (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ)
    (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ)
    (hF : aeval τ F ≠ 0) (hS : S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)))
    (hz : ∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i))
    (hprime : ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (𝔮 : Ideal (MvPolynomial σ ℂ))
    (hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮)
    (hFq : map (algebraMap ℚ ℂ) F ∉ 𝔮)
    (E : Type) [Field E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮) :
    (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
  have hau : ∀ G : MvPolynomial σ ℚ,
      aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := aeval_eq_image π
  have hunit : IsUnit (aeval (fun q => π (X q)) F) := by
    rw [hau]
    exact IsUnit.mk0 _ (fun h => hFq ((hπ _).1 h))
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv Ω σ τ F S E (fun q => π (X q)) hF hS
    (fun G hG => by rw [hau]; exact (hπ _).2 (hker G hG)) hunit
  have hτS : ∀ q, τ q ∈ S := fun q => by
    rw [hS]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  let τS : σ → S := fun q => ⟨τ q, hτS q⟩
  have hcoe : ∀ G : MvPolynomial σ ℚ, ((aeval τS G : S) : Ω) = aeval τ G := by
    intro G
    have h : S.val.comp (aeval τS) = aeval τ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [τS]
    exact DFunLike.congr_fun h G
  have hq : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ s, s ∈ RingHom.ker φ ↔ φ s = 0 := fun s => RingHom.mem_ker
  have hleft : (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      (∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ RingHom.ker φ) := by
    constructor
    · intro h g hg s hs
      rw [hmem, hφ (map (Int.castRingHom ℚ) g) s (by rw [hs, aeval_int_eq]), hau, map_map_int]
      exact (hπ _).2 (h g hg)
    · intro h g hg
      have hs := hcoe (map (Int.castRingHom ℚ) g)
      have h0 := h g hg (aeval τS (map (Int.castRingHom ℚ) g)) (by rw [hs, aeval_int_eq])
      rw [hmem, hφ _ _ hs, hau, map_map_int] at h0
      exact (hπ _).1 h0
  have hright : ∀ i, z i ∈ RingHom.ker φ ↔ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
    intro i
    have hzi : φ (z i * (aeval τS F) ^ N i) = aeval (fun q => π (X q)) (Z i) :=
      hφ _ _ (by push_cast; rw [hcoe, hz])
    have hfS : φ (aeval τS F) = aeval (fun q => π (X q)) F := hφ _ _ (hcoe F)
    rw [map_mul, map_pow, hfS] at hzi
    have hf0 : aeval (fun q => π (X q)) F ≠ 0 := hunit.ne_zero
    rw [hmem, ← hπ, ← hau, ← hzi]
    simp [hf0]
  rw [hleft, hprime _ hq]
  exact exists_congr fun i => and_congr_right fun _ => hright i
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
