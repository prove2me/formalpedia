-- Prove2me | solution 1 for GlobalTheory.GramCount.dep_idem_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:32.88141+00:00
-- url     : https://prove2.me/submissions/bf3a368d-bd23-4413-a287-161621f05acc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Theorems.Thm_GlobalTheory_GramCount_dep_isUnit_of_skew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {ε ε' : B} (h1 : ε + c ε = 1) (h2 : ε * c ε = 0)
    (h1' : ε' + c ε' = 1) (h2' : ε' * c ε' = 0) : ε' = ε ∨ ε' = c ε := by
  by_cases h : ε' = ε
  · exact Or.inl h
  right
  have hu : IsUnit (ε' - ε) := dep_isUnit_of_skew c hc hω hf
    (by rw [map_sub]; linear_combination h1' - h1) (sub_ne_zero.2 h)
  have : (ε' - ε) * (ε' - c ε) = 0 := by
    linear_combination h2 - h2' + ε' * h1' - ε' * h1
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)
end GlobalTheory.GramCount
