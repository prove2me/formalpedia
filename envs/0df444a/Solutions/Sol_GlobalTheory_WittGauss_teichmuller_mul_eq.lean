-- Prove2me | solution 1 for GlobalTheory.WittGauss.teichmuller_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:51.6478+00:00
-- url     : https://prove2.me/submissions/80db9a49-d04d-4f1e-88e7-4e2c83fd8527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_map_scaleCoeff
import Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_int

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
    (x : WittVector p S) : teichmuller p t * x = scaleCoeff p t x := by
  obtain ⟨t, rfl⟩ := MvPolynomial.counit_surjective S t
  obtain ⟨x, rfl⟩ := WittVector.map_surjective (p := p)
    (MvPolynomial.counit S) (MvPolynomial.counit_surjective S) x
  have := congrArg (WittVector.map (MvPolynomial.counit S)) (teichmuller_mul_int p t x)
  rwa [map_mul, map_teichmuller, map_scaleCoeff] at this
end GlobalTheory.WittGauss
