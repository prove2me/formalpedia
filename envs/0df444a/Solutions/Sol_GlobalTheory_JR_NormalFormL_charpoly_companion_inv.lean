-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.charpoly_companion_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:53.771733+00:00
-- url     : https://prove2.me/submissions/6fa0a919-0833-441e-8d5f-db8917747cf6

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_coeff

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
theorem _root_.solution (Y : Gl r k) : (companion (inv Y).1).charpoly = Y.1.charpoly := by
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n r with h | h | h
  · exact charpoly_companion_coeff _ ⟨n, h⟩
  · subst h
    have h1 := (charpoly_monic (companion (inv Y).1)).leadingCoeff
    have h2 := (charpoly_monic Y.1).leadingCoeff
    rw [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at h1 h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt] <;>
      simpa using h
end GlobalTheory.JR.NormalFormL
