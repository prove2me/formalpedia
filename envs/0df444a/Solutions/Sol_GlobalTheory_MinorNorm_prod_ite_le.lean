-- Prove2me | solution 1 for GlobalTheory.MinorNorm.prod_ite_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:33.300287+00:00
-- url     : https://prove2.me/submissions/e67f3221-2bd1-47f6-aa83-3d65522ab780

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

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
theorem _root_.solution (K : Fin l) (g : Fin l → ℚ) :
    (∏ i : Fin l, if i ≤ K then g i else 1) =
      ∏ t : Fin (K + 1), g (Fin.castLE K.2 t) := by
  rw [← Finset.prod_filter]
  symm
  refine Finset.prod_bij (fun t _ => Fin.castLE K.2 t) ?_ ?_ ?_ ?_
  · intro t _
    have := t.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_castLE]
    omega
  · intro t _ t' _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have : (j : ℕ) ≤ K := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro t _
    rfl
end GlobalTheory.MinorNorm
