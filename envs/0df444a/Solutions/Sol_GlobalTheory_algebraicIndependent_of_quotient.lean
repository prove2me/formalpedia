-- Prove2me | solution 1 for GlobalTheory.algebraicIndependent_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:56.305397+00:00
-- url     : https://prove2.me/submissions/dc8abe0c-4dd1-4a3d-b4cf-0a203adc06b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Theorems.Thm_GlobalTheory_exists_C_mul_eq_C_mul_coeff_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {ι o S T : Type*} [CommRing o] [IsDedekindDomain o]
    [CommRing S] [Algebra o S] [Module.IsTorsionFree o S] {J : Ideal o} (hJ : J ≠ ⊤)
    [CommRing T] [Algebra (o ⧸ J) T] (ψ : S →+* T)
    (hψ : ∀ r : o, ψ (algebraMap o S r) = algebraMap (o ⧸ J) T (Ideal.Quotient.mk J r))
    {f : ι → S} (hf : AlgebraicIndependent (o ⧸ J) (fun i => ψ (f i))) :
    AlgebraicIndependent o f := by
  rw [algebraicIndependent_iff] at hf ⊢
  intro G hG
  by_contra hne
  obtain ⟨b, u, G', hb, hbu, m, hm⟩ := exists_C_mul_eq_C_mul_coeff_notMem hJ hne
  have h1 : aeval f G' = 0 := by
    have h2 := congrArg (aeval f : MvPolynomial ι o →ₐ[o] S) hbu
    rw [map_mul, map_mul, hG, mul_zero, aeval_C, ← Algebra.smul_def] at h2
    exact (smul_eq_zero.mp h2).resolve_left hb
  have h3 : (aeval (fun i => ψ (f i)) : MvPolynomial ι (o ⧸ J) →ₐ[o ⧸ J] T).toRingHom.comp
      (map (Ideal.Quotient.mk J)) = ψ.comp (aeval f : MvPolynomial ι o →ₐ[o] S).toRingHom := by
    ext r <;> simp [hψ]
  have h4 := hf (map (Ideal.Quotient.mk J) G') (by
    have := RingHom.congr_fun h3 G'
    simpa [h1] using this)
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h4, coeff_zero]
end GlobalTheory
