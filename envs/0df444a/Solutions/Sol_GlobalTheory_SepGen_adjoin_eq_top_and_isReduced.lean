-- Prove2me | solution 1 for GlobalTheory.SepGen.adjoin_eq_top_and_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:45.742909+00:00
-- url     : https://prove2.me/submissions/34002709-5b7d-4722-9c7b-26134f7b1b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top
import Theorems.Thm_GlobalTheory_SepGen_isReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]
namespace GlobalTheory.SepGen
theorem _root_.solution : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable →
    Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A :=
  fun _ _ _ _ _ _ y hs => ⟨adjoin_eq_top y hs, isReduced y hs⟩
end GlobalTheory.SepGen
