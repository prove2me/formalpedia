-- Prove2me | solution 1 for GlobalTheory.SepGenElt.exists_aeval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:33.941281+00:00
-- url     : https://prove2.me/submissions/36acd5b9-dc23-41b4-8e74-a6037f2b8539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparable
import Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGenElt
namespace GlobalTheory.SepGenElt
theorem _root_.solution : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  intro E A _ _ _ _ g hs x
  have hx : x ∈ Algebra.adjoin E ({g} : Set A) := by
    rw [GlobalTheory.SepGen.adjoin_eq_top g hs]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  exact hx
end GlobalTheory.SepGenElt
