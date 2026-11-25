-- Prove2me | solution 1 for GlobalTheory.GramCount.dep_unit_or_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:37.055979+00:00
-- url     : https://prove2.me/submissions/81fc9530-a8e5-4f29-9798-c835b3070c65

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
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {a : B} (h0 : a ≠ 0) :
    (∃ b, b * a = 1) ∨ ∃ b, (b * a) + c (b * a) = 1 ∧ (b * a) * c (b * a) = 0 := by
  by_cases hu : IsUnit a
  · exact Or.inl hu.exists_left_inv
  right
  have h1 : a * c a = 0 := by
    by_contra h
    exact hu (isUnit_of_mul_isUnit_left (hf _ (by rw [map_mul, hc, mul_comm]) h))
  have h2 : a + c a ≠ 0 := fun h =>
    hu (dep_isUnit_of_skew c hc hω hf (by linear_combination h) h0)
  have h3 : c (a + c a) = a + c a := by rw [map_add, hc, add_comm]
  obtain ⟨b, hb⟩ := (hf _ h3 h2).exists_left_inv
  have hb' : c b * (a + c a) = 1 := by
    have := congrArg c hb
    rwa [map_mul, h3, map_one] at this
  have hcb : c b = b := by linear_combination b * hb' - c b * hb
  refine ⟨b, ?_, ?_⟩
  · rw [map_mul, hcb]; linear_combination hb
  · rw [map_mul, hcb]; linear_combination b * b * h1
end GlobalTheory.GramCount
