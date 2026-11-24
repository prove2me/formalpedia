-- Prove2me | solution 1 for GlobalTheory.MinorNorm.hookProd_addCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:59.868508+00:00
-- url     : https://prove2.me/submissions/b921437b-fe5f-4010-89c8-98885246489f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_prod_Ioi_eq
import Theorems.Thm_GlobalTheory_MinorNorm_telescope
import Theorems.Thm_GlobalTheory_MinorNorm_addCol_antitone
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
theorem _root_.solution {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) (hK : ∀ i, K < i → a i = 0) :
    hookProd (addCol a K) =
      (∏ i : Fin l, if i ≤ K then ((a i : ℚ) + 1 + (K : ℕ) - (i : ℕ)) else 1) * hookProd a := by
  unfold hookProd
  rw [← mul_div_assoc, div_eq_div_iff (hookDen_pos (addCol_antitone ha K)).ne' (hookDen_pos ha).ne']
  unfold hookDen
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ≤ K
  · have hsplit : ∀ g : Fin l → ℚ, ∏ j ∈ Finset.Ioi i, g j =
        (∏ j ∈ Finset.Ioc i K, g j) * ∏ j ∈ Finset.Ioi K, g j := by
      intro g
      have hu : Finset.Ioi i = Finset.Ioc i K ∪ Finset.Ioi K := by
        ext j
        have : (i : ℕ) ≤ K := hi
        simp only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Ioc, Fin.lt_def, Fin.le_def]
        omega
      rw [hu, Finset.prod_union]
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact absurd (Finset.mem_Ioc.mp h1).2 (not_le.mpr (Finset.mem_Ioi.mp h2))
    have e1 : ∏ j ∈ Finset.Ioc i K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      simp [addCol, hi, (Finset.mem_Ioc.mp hj).2]
    have e2 : ∏ j ∈ Finset.Ioi K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + 1 + j) := by
      rw [← prod_Ioi_eq]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ioi.mp hj
      simp only [addCol, hi, if_true, not_le.mpr hj', if_false, hK j hj']
      push_cast
      ring
    have e3 : ∏ j ∈ Finset.Ioi K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + j) := by
      rw [← prod_Ioi_eq]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ioi.mp hj
      simp only [hK j hj']
      push_cast
      ring
    have e4 : ((addCol a K i + (l - ((i : ℕ) + 1))).factorial : ℚ) =
        ((a i : ℚ) - (i : ℕ) + l) * (a i + (l - ((i : ℕ) + 1))).factorial := by
      have : addCol a K i + (l - ((i : ℕ) + 1)) = (a i + (l - ((i : ℕ) + 1))) + 1 := by
        simp only [addCol, hi, if_true]; omega
      rw [this, Nat.factorial_succ]
      push_cast [Nat.cast_sub (show (i : ℕ) + 1 ≤ l from i.2)]
      ring
    have t := telescope ((a i : ℚ) - (i : ℕ)) ((K : ℕ) + 1) l K.2
    rw [hsplit, hsplit, e1, e2, e3, e4, if_pos hi]
    push_cast at t
    linear_combination (-((a i + (l - ((i : ℕ) + 1))).factorial : ℚ) *
      ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ))) * t
  · rw [if_neg hi, one_mul]
    have e : ∀ j, i ≤ j → addCol a K j = a j := fun j hj => by
      simp [addCol, show ¬ j ≤ K from fun h => hi (hj.trans h)]
    rw [e i le_rfl]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [e j (Finset.mem_Ioi.mp hj).le]
end GlobalTheory.MinorNorm
