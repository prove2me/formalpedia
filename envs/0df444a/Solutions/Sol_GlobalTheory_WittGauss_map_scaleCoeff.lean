-- Prove2me | solution 1 for GlobalTheory.WittGauss.map_scaleCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:41.295116+00:00
-- url     : https://prove2.me/submissions/89f9ed25-bf47-4759-831f-f586e0f0ee2b

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {S S' : Type} [CommRing S] [CommRing S']
    (f : S →+* S') (t : S) (x : WittVector p S) :
    WittVector.map f (scaleCoeff p t x) = scaleCoeff p (f t) (WittVector.map f x) := by
  ext n
  simp [scaleCoeff, WittVector.map_coeff]
end GlobalTheory.WittGauss
