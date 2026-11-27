-- Prove2me | solution 1 for GlobalTheory.natCast_mul_coeff_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:41.469345+00:00
-- url     : https://prove2.me/submissions/3538d59b-f69f-4d92-87ec-b5cfbf1c713e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NatCastMulCoeffCharpolyRev
import Theorems.Thm_GroundTheory_Global_coe_derivative_charpolyRev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | j
  · simp
  · have h := congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg,
      PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    have e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i := fun i _ => by omega
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)
end GlobalTheory
