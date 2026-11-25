-- Prove2me | solution 1 for GlobalTheory.GramCount.dep_isUnit_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:21.965866+00:00
-- url     : https://prove2.me/submissions/3d178c44-3d4d-479c-9fc4-c72a0185b044

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Theorems.Thm_GlobalTheory_GramCount_exists_trace_one


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
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {u : B} (hu : c u = -u) (h0 : u ≠ 0) : IsUnit u := by
  obtain ⟨θ, e, -, he, hce⟩ := exists_trace_one c hc hω
  refine isUnit_of_mul_isUnit_left (y := e) (hf _ ?_ ?_)
  · rw [map_mul, hu, hce]; ring
  · intro h
    exact h0 (he.mul_left_eq_zero.1 h)
end GlobalTheory.GramCount
