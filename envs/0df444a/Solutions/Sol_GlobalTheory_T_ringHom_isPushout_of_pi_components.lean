-- Prove2me | solution 1 for GlobalTheory.T.ringHom_isPushout_of_pi_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:59.597212+00:00
-- url     : https://prove2.me/submissions/1a7f1fc0-e786-4c90-8398-a28c18f28f41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomIsPushoutOfPiComponents
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomIsPushoutOfPiComponentsStatement
import Theorems.Thm_GlobalTheory_isPushout_of_pi_components


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A'] [CommRing P'] {n : ℕ}
    {Pi P'i : Fin n → Type} [∀ i, CommRing (Pi i)] [∀ i, CommRing (P'i i)]
    (f : A →+* P) (k : A →+* A') (k' : P →+* P') (h' : A' →+* P')
    (g : ∀ i, P →+* Pi i) (g' : ∀ i, P' →+* P'i i) (kk : ∀ i, Pi i →+* P'i i) (hh : ∀ i, A' →+* P'i i),
    Function.Bijective (fun (x : P) (i : Fin n) => g i x) →
    Function.Bijective (fun (x : P') (i : Fin n) => g' i x) →
    (∀ i, (g' i).comp k' = (kk i).comp (g i)) → (∀ i, (g' i).comp h' = hh i) →
    (∀ i, CategoryTheory.IsPushout (CommRingCat.ofHom ((g i).comp f)) (CommRingCat.ofHom k)
      (CommRingCat.ofHom (kk i)) (CommRingCat.ofHom (hh i))) →
    CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  first | exact @GlobalTheory.isPushout_of_pi_components | exact GlobalTheory.isPushout_of_pi_components | (intros; apply GlobalTheory.isPushout_of_pi_components <;> assumption)
end _root_.GlobalTheory.T
