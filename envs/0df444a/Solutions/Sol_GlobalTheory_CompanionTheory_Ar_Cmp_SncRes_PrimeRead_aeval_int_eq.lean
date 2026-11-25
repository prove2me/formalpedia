-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.aeval_int_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:11.883315+00:00
-- url     : https://prove2.me/submissions/6433bec2-47e3-4746-b9aa-569d08a3df17

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes

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
theorem _root_.solution {σ Ω : Type} [CommRing Ω] [Algebra ℚ Ω] (τ : σ → Ω)
    (g : MvPolynomial σ ℤ) : aeval τ g = aeval τ (map (Int.castRingHom ℚ) g) := by
  have h : (aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom =
      (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_int
        ((aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom.comp C)
        (((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp
          (map (Int.castRingHom ℚ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h g
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
