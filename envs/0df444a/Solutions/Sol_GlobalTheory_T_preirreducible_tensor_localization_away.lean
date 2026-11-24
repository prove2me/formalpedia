-- Prove2me | solution 1 for GlobalTheory.T.preirreducible_tensor_localization_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:52.108597+00:00
-- url     : https://prove2.me/submissions/04213fd7-194d-4b92-9d7d-69e0c35b898b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAwayStatement
import Theorems.Thm_GlobalTheory_preirreducibleSpace_primeSpectrum_tensor_localizationAway


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  first | exact @GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | exact GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | (intros; apply GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway <;> assumption)
end _root_.GlobalTheory.T
