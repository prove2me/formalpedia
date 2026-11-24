-- Prove2me | solution 1 for GlobalTheory.RowDet.minor_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:33.356415+00:00
-- url     : https://prove2.me/submissions/35591040-7e56-4f7c-8ab7-e9c26157e518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Theorems.Thm_GlobalTheory_RowDet_minor_not_dvd
import Theorems.Thm_GlobalTheory_RowDet_irreducible_det

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
theorem _root_.solution {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e) :
    ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  cases n with
  | zero => rw [Matrix.det_isEmpty]; exact ⟨one_ne_zero, isRelPrime_one_left⟩
  | succ n =>
    have h := irreducible_det (R := R) n (fun p => e (p.1.castSucc, p.2.castSucc))
      (fun p q hpq => by
        have := he hpq
        simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
        exact Prod.ext this.1 this.2)
    exact ⟨h.ne_zero, h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he)⟩
end GlobalTheory.RowDet
