-- Prove2me | solution 1 for GlobalTheory.UnitWitt.exists_unitary_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:07.262558+00:00
-- url     : https://prove2.me/submissions/73ae7ece-28cc-47c1-bfb4-0c3a344519bb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Theorems.Thm_GlobalTheory_UnitWitt_exists_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
namespace GlobalTheory.UnitWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  by_cases ha : star (u - v) ⬝ᵥ u = 0
  · have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at ha; exact ha.symm
    have hc' : star (-u) ⬝ᵥ (-u) = star v ⬝ᵥ v := by simpa using hc
    have ha' : star (-u - v) ⬝ᵥ (-u) ≠ 0 := by
      have : star (-u - v) ⬝ᵥ (-u) = 2 * (star u ⬝ᵥ u) := by
        simp only [star_sub, star_neg, sub_dotProduct, neg_dotProduct, dotProduct_neg, hvu]
        ring
      rw [this]; exact mul_ne_zero h2 h0
    obtain ⟨g, hg⟩ := exists_of_ne (-u) v hc' ha'
    refine ⟨⟨-g.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_neg, neg_mul_neg]; exact mem_unitaryGroup_iff'.1 g.2
    · show (-g.1) *ᵥ u = v
      rw [← hg, neg_mulVec, mulVec_neg]
  · exact exists_of_ne u v hc ha
end GlobalTheory.UnitWitt
