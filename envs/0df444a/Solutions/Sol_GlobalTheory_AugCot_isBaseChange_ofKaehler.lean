-- Prove2me | solution 1 for GlobalTheory.AugCot.isBaseChange_ofKaehler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:34.660026+00:00
-- url     : https://prove2.me/submissions/04c7e484-b407-4af6-98b7-a2436befc73e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
variable {N : Type*} [AddCommGroup N] [Module R N]
variable [Algebra A R] (h : ∀ a, algebraMap A R a = ε a)
namespace GlobalTheory.AugCot
theorem _root_.solution :
    haveI := isScalarTower_of_algebraMap_eq ε h
    IsBaseChange R (ofKaehler ε) :=
  haveI := isScalarTower_of_algebraMap_eq ε h
  IsBaseChange.of_equiv (kaehlerEquiv ε h).symm (fun m => by simp)
end GlobalTheory.AugCot
