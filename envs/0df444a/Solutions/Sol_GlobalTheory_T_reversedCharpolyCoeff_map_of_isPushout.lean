-- Prove2me | solution 1 for GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:04.204158+00:00
-- url     : https://prove2.me/submissions/df25e690-48cf-4a2e-a42f-1ff7f7bf1ac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushoutStatement
import Theorems.Thm_GlobalTheory_NormalDescent_normCoeff_map_of_isPushout


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | exact GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.normCoeff_map_of_isPushout <;> assumption)
end _root_.GlobalTheory.T
