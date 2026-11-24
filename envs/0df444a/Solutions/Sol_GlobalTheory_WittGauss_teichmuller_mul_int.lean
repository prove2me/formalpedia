-- Prove2me | solution 1 for GlobalTheory.WittGauss.teichmuller_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:03.523832+00:00
-- url     : https://prove2.me/submissions/49246343-1bda-4759-9303-50473b630660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_map_scaleCoeff
import Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_rat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
namespace GlobalTheory.WittGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℤ)
    (x : WittVector p (MvPolynomial S ℤ)) : teichmuller p t * x = scaleCoeff p t x := by
  refine WittVector.map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  rw [map_mul, map_teichmuller, map_scaleCoeff, teichmuller_mul_rat]
end GlobalTheory.WittGauss
