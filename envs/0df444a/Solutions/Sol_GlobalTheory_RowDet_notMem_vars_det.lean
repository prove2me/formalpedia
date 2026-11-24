-- Prove2me | solution 1 for GlobalTheory.RowDet.notMem_vars_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:23.708859+00:00
-- url     : https://prove2.me/submissions/30bb916c-0c98-4080-80b5-e08a9e079a29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Theorems.Thm_GlobalTheory_RowDet_det_mem_subalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.RowDet
namespace GlobalTheory.RowDet
theorem _root_.solution {R σ : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (a : σ) (M : Matrix m m (MvPolynomial σ R)) (h : ∀ i j, a ∉ (M i j).vars) :
    a ∉ M.det.vars := by
  have : M.det ∈ supported R ({a}ᶜ : Set σ) := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    rw [mem_supported]
    intro b hb hba
    rw [Set.mem_singleton_iff] at hba
    exact h i j (hba ▸ hb)
  rw [mem_supported] at this
  intro ha
  exact this ha rfl
end GlobalTheory.RowDet
