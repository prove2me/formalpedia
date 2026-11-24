-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:34.883139+00:00
-- url     : https://prove2.me/submissions/7b10c8dc-0ed3-4f02-91e1-2a43f5cba094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound
namespace GlobalTheory.CompleteHomogeneousBound
theorem _root_.solution {n : ℕ} (β : Fin n → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk fun k => β i ^ k : ℂ⟦X⟧)) =
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i := by
  rw [coeff_prod]
  simp only [coeff_mk]
  refine Finset.sum_bij' (fun l _ => (l : Fin n → ℕ))
    (fun a _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using hl
  · intro a ha
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using ha
  · intro l _
    simp
  · intro a _
    simp
  · intro l _
    rfl
end GlobalTheory.CompleteHomogeneousBound
