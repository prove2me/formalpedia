-- Prove2me | solution 1 for GlobalTheory.wittVector_coeff_pow_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.72342+00:00
-- url     : https://prove2.me/submissions/ef49dc14-2264-47ae-a430-02178abd7880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by
  intro m
  induction m with
  | zero => intro t j hj; omega
  | succ m ih =>
    intro t j hj
    have h : (l : WittVector l R) ^ (m + 1) * t
        = verschiebung (frobenius ((l : WittVector l R) ^ m * t)) := by
      rw [verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact verschiebung_coeff_zero _
    | succ j =>
      rw [verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]
      exact zero_pow hl.out.ne_zero
end GlobalTheory
