-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.map_map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:58.79318+00:00
-- url     : https://prove2.me/submissions/092b6f8d-ebd7-486a-a9e1-3526cb0cc6ce

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
theorem _root_.solution {σ : Type} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [MvPolynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
