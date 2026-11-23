-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.pow_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:32.001321+00:00
-- url     : https://prove2.me/submissions/da4b1e49-22be-4f47-be4e-adcf59bf82de

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (M : Matrix (Fin r) (Fin r) k) :
    M ^ r = - ∑ l ∈ Finset.range r, M.charpoly.coeff l • M ^ l := by
  have h0 := aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h0
  have h1 : M.charpoly.coeff r = 1 := by
    have := (charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [h1, one_smul] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0
end GlobalTheory.JR.NormalFormL
