-- Prove2me | solution 1 for GlobalTheory.RowDet.irreducible_det_of_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:13.772107+00:00
-- url     : https://prove2.me/submissions/5774f87e-606d-43fd-93cf-499e50721f6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Theorems.Thm_GlobalTheory_RowDet_notMem_vars_det
import Theorems.Thm_GlobalTheory_RowDet_det_updateRow_single

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
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e)
    (h0 : ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0)
    (h : IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det) :
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  set A := (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)) with hA
  let r : Fin (n + 1) → MvPolynomial σ R := fun k => if k = Fin.last n then 0 else A (Fin.last n) k
  have hD : A.det = (A.submatrix Fin.castSucc Fin.castSucc).det * X (e (Fin.last n, Fin.last n))
      + (A.updateRow (Fin.last n) r).det := by
    rw [← det_updateRow_single, mul_comm, ← Matrix.det_updateRow_smul,
      ← Matrix.det_updateRow_add]
    congr 1
    rw [eq_comm]
    convert Matrix.updateRow_eq_self A (Fin.last n)
    ext1 k
    by_cases hk : k = Fin.last n
    · subst hk; simp [r, A]
    · simp [r, hk]
  rw [hD] at h ⊢
  refine irreducible_mul_X_add _ _ _ h0 ?_ ?_ ?_
  · refine notMem_vars_det _ _ fun i j => ?_
    simp [A, vars_X, he.eq_iff, (Fin.castSucc_lt_last j).ne']
  · refine notMem_vars_det _ _ fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      by_cases hj : j = Fin.last n
      · simp [r, hj]
      · simp [r, hj, A, vars_X, he.eq_iff, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, A, vars_X, he.eq_iff, Ne.symm hi]
  · intro c hc1 hc2
    exact h hc1 (dvd_add (hc1.mul_right _) hc2)
end GlobalTheory.RowDet
