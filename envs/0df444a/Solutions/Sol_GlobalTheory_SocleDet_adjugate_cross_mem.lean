-- Prove2me | solution 1 for GlobalTheory.SocleDet.adjugate_cross_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:40.867007+00:00
-- url     : https://prove2.me/submissions/e2fdae0e-fe97-4866-8c98-5bdc0a5605bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Theorems.Thm_GlobalTheory_SocleDet_det_mul_sub_adjugate_mul_mem
import Theorems.Thm_GlobalTheory_SocleDet_adjugate_updateRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SocleDet
theorem _root_.solution (I : Ideal R) (M : Matrix n n R) (x : n → R) (i j l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.adjugate j i * x l - M.adjugate l i * x j ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I (M.updateRow i (Pi.single j 1)) x i l (by
    intro r hr
    have : (M.updateRow i (Pi.single j 1) *ᵥ x) r = (M *ᵥ x) r := by
      simp [mulVec, updateRow_ne hr]
    rw [this]; exact h r hr)
  rw [adjugate_updateRow, ← adjugate_apply] at this
  have e : (M.updateRow i (Pi.single j 1) *ᵥ x) i = x j := by
    simp [mulVec]
  rwa [e] at this
end GlobalTheory.SocleDet
