-- Prove2me | solution 1 for GlobalTheory.MinorNorm.hookProd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:00.709807+00:00
-- url     : https://prove2.me/submissions/93585ab2-6b2b-4988-8b9e-b2ce4085bf48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_prod_Ioi_eq
import Theorems.Thm_GlobalTheory_MinorNorm_prod_sub_eq_factorial
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CornerMinors_hookDen_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
namespace GlobalTheory.MinorNorm
theorem _root_.solution : hookProd (0 : Fin l → ℕ) = 1 := by
  unfold hookProd
  rw [div_eq_one_iff_eq (hookDen_pos (a := 0) antitone_const).ne']
  unfold hookDen
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, zero_add, Nat.cast_zero, sub_self]
  rw [prod_Ioi_eq i fun j => (j : ℚ) - (i : ℕ), prod_sub_eq_factorial _ _ i.2]
end GlobalTheory.MinorNorm
