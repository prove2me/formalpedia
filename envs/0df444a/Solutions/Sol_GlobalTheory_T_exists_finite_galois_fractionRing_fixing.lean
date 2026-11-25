-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_galois_fractionRing_fixing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:20:37.139155+00:00
-- url     : https://prove2.me/submissions/3b14f44e-b3a2-4959-bc0e-605d66da22fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRingStatement
import Theorems.Thm_GlobalTheory_finiteGalois_fractionRing_of_isFractionRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  first | exact @GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | exact GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | (intros; apply GlobalTheory.finiteGalois_fractionRing_of_isFractionRing <;> assumption)
end _root_.GlobalTheory.T
