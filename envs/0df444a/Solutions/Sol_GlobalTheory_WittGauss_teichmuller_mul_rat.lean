-- Prove2me | solution 1 for GlobalTheory.WittGauss.teichmuller_mul_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:10.614637+00:00
-- url     : https://prove2.me/submissions/f7ae2c57-30d7-4e98-ba13-d473fe623edc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_ghostComponent_scaleCoeff

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℚ)
    (x : WittVector p (MvPolynomial S ℚ)) : teichmuller p t * x = scaleCoeff p t x := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial S ℚ)).1
  ext1 n
  simp only [map_mul, ghostMap_apply, ghostComponent_teichmuller, ghostComponent_scaleCoeff]
end GlobalTheory.WittGauss
