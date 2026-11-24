-- Prove2me | solution 1 for GlobalTheory.SepGen.aeval_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:32.934828+00:00
-- url     : https://prove2.me/submissions/54396c67-3bd1-4b4d-b290-d630a8cae50f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable

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
theorem _root_.solution (y : A) : aeval y (LinearMap.mulLeft E y).charpoly = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y (LinearMap.mulLeft E y).charpoly
  have h2 : aeval (Algebra.lmul E A y) (LinearMap.mulLeft E y).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  rw [h2] at h
  simpa using (LinearMap.congr_fun h 1).symm
end GlobalTheory.SepGen
