-- Prove2me | solution 1 for GlobalTheory.MinorNorm.prod_Ioi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:14.098291+00:00
-- url     : https://prove2.me/submissions/9431f9f4-1eba-447c-88ba-1cb0967607d0

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
theorem _root_.solution (K : Fin l) (g : ℕ → ℚ) :
    ∏ j ∈ Finset.Ioi K, g j = ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, g j := by
  refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
  · intro j hj
    have : K < j := Finset.mem_Ioi.mp hj
    exact Finset.mem_Ico.mpr ⟨this, j.2⟩
  · intro j _ j' _ h
    exact Fin.ext h
  · intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    exact ⟨⟨j, h2⟩, Finset.mem_Ioi.mpr h1, rfl⟩
  · intro j _
    rfl
end GlobalTheory.MinorNorm
