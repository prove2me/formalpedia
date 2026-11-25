-- Prove2me | solution 1 for GlobalTheory.ClassMin.map_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:34.90473+00:00
-- url     : https://prove2.me/submissions/1a8ee217-7e09-49c9-833c-46f83d205c72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_mul_map_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hQ : ∀ x, 0 ≤ Q x) {ι : Type*} (s : Finset ι) (v : ι → X) :
    Q (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, Q (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, add_comm (v i)]
    have h1 := mul_map_add_le hQ s.card (∑ i ∈ s, v i) (v i)
    push_cast at h1 ⊢
    refine le_of_mul_le_mul_left (h1.trans ?_) hc
    nlinarith [mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ s.card + 1 by positivity)]
end GlobalTheory.ClassMin
