-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.pdiag_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:15.21103+00:00
-- url     : https://prove2.me/submissions/75f2a857-a52d-4c20-a588-92386849b159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
import Theorems.Thm_GlobalTheory_PoincareBounds_poincareGram_eq
import Theorems.Thm_GlobalTheory_PoincareBounds_pdiag_nonneg
import Theorems.Thm_GlobalTheory_PoincareBounds_gnorm_diag_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds
namespace GlobalTheory.PoincareBounds
theorem _root_.solution {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (ξ : Fin n → ℂ) (k : Fin n) :
    pdiag a z k * ‖ξ k‖ ^ 2 ≤ gnorm (poincareGram a z) ξ ^ 2 := by
  rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg a z)]
  exact Finset.single_le_sum (f := fun k => pdiag a z k * ‖ξ k‖ ^ 2)
    (fun j _ => mul_nonneg (pdiag_nonneg a z j) (by positivity)) (Finset.mem_univ k)
end GlobalTheory.PoincareBounds
