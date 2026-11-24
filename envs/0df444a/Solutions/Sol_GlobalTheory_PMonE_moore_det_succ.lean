-- Prove2me | solution 1 for GlobalTheory.PMonE.moore_det_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:29.406184+00:00
-- url     : https://prove2.me/submissions/0b8d0361-eb66-49ca-89d6-6050caa27360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {k : ℕ} (lam : Fin (k + 1) → F) :
    (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det =
      (-1) ^ k * lam (Fin.last k) * (Matrix.of fun r j : Fin k =>
        (lam j.castSucc ^ p - lam (Fin.last k) ^ (p - 1) * lam j.castSucc) ^ p ^ (r : ℕ)).det := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set t := lam (Fin.last k) with ht
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
    Matrix.of fun r j => Fin.cases (motive := fun _ => F) (lam j)
      (fun s => (lam j ^ p - t ^ (p - 1) * lam j) ^ p ^ (s : ℕ)) r
  have hB : (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun s => (t ^ (p - 1)) ^ p ^ (s : ℕ)) ?_ ?_
    · intro j; simp [B]
    · intro i j
      simp only [B, Matrix.of_apply, Fin.cases_succ, Fin.val_succ, Fin.val_castSucc]
      rw [sub_pow_char_pow, mul_pow, ← pow_mul (lam j) p, pow_succ' p]
      ring
  have h0 : t ^ p - t ^ (p - 1) * t = 0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.le, sub_self]
  rw [hB, Matrix.det_succ_column B (Fin.last k), Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · congr 1
    · simp [B, ht]
    · congr 1
      ext r j
      simp [B]
  · intro i _
    have : B i.succ (Fin.last k) = 0 := by
      simp only [B, Matrix.of_apply, Fin.cases_succ, ← ht, h0]
      exact zero_pow (pow_ne_zero _ (by omega))
    rw [this]; simp
end GlobalTheory.PMonE
