-- Prove2me | solution 1 for GlobalTheory.RowDet.irreducible_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:55:59.741424+00:00
-- url     : https://prove2.me/submissions/e6fcfb2d-ceaa-402e-b47a-a5c9c798f191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Theorems.Thm_GlobalTheory_RowDet_minor_not_dvd
import Theorems.Thm_GlobalTheory_RowDet_irreducible_det_of_isRelPrime

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
theorem _root_.solution {R σ : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    ∀ (e : Fin (n + 1) × Fin (n + 1) → σ), Function.Injective e →
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  induction n with
  | zero =>
    intro e he
    refine irreducible_det_of_isRelPrime e he ?_ ?_
    · simp
    · rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  | succ n ih =>
    intro e he
    have h := ih (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by
      have := he hpq
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
      exact Prod.ext this.1 this.2)
    exact irreducible_det_of_isRelPrime e he h.ne_zero
      (h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he))
end GlobalTheory.RowDet
