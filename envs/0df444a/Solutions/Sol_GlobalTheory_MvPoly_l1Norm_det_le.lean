-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:49.550993+00:00
-- url     : https://prove2.me/submissions/be59904f-8d21-42f4-8308-531de066cf40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * R ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [← Fintype.card_perm, ← nsmul_eq_mul, ← card_univ (α := Equiv.Perm ι)]
  refine sum_le_card_nsmul _ _ _ fun π _ ↦ ?_
  have h1 : l1Norm (Equiv.Perm.sign π • ∏ i, M (π i) i) = l1Norm (∏ i, M (π i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [h1]
  refine (l1Norm_prod_le _ _).trans ?_
  rw [← card_univ, ← prod_const]
  exact prod_le_prod (fun _ _ ↦ l1Norm_nonneg _) fun _ _ ↦ h _ _
end GlobalTheory.MvPoly
