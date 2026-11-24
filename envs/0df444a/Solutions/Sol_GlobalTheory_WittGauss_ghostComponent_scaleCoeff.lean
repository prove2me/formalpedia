-- Prove2me | solution 1 for GlobalTheory.WittGauss.ghostComponent_scaleCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:53.110801+00:00
-- url     : https://prove2.me/submissions/827c0ea9-bada-4c6b-9e1a-a61c82c2d783

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) (n : ℕ) :
    ghostComponent n (scaleCoeff p t x) = t ^ p ^ n * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial, scaleCoeff, WittVector.coeff_mk,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h : i + (n - i) = n := by
    have := Finset.mem_range.1 hi
    omega
  rw [mul_pow, ← pow_mul, ← pow_add, h]
  ring
end GlobalTheory.WittGauss
