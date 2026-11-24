-- Prove2me | solution 1 for GlobalTheory.TriSqrt.det_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:08.263807+00:00
-- url     : https://prove2.me/submissions/6ec834a5-d207-4db6-acc6-23f52ae2bf11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
import Theorems.Thm_GlobalTheory_TriSqrt_det_eq_prod_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.TriSqrt
namespace GlobalTheory.TriSqrt
theorem _root_.solution {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') (d : n → ℝ)
    (S : Matrix n n ℂ) (hs : ∀ j j', S j j' ≠ 0 → t j = t j' ∧ w j ≤ w j')
    (p : n → Prop) [DecidablePred p] (hp : ∀ c a, S c a ≠ 0 → p a → p c) :
    ((Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val).det
      = ((∏ c ∈ Finset.univ.filter p, ‖S c c‖ ^ 2 * d c : ℝ) : ℂ) := by
  set T : Matrix {x // p x} {x // p x} ℂ := S.submatrix Subtype.val Subtype.val with hT
  have e : (Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val
      = Tᵀ * ((Matrix.diagonal fun j => ((d j.1 : ℝ) : ℂ)) * T.map (starRingEnd ℂ)) := by
    ext a a'
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hT,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)
      (fun c => S c a * ((d c : ℂ) * (starRingEnd ℂ) (S c a')))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
    have : S c a = 0 := by
      by_contra hne
      exact hc (by simpa using hp c a hne a.2)
    rw [this, zero_mul]
  have hdT : T.det = ∏ c, T c c :=
    det_eq_prod_diag (fun c => t c.1) (fun c => w c.1)
      (fun c c' h1 h2 => Subtype.ext (hinj _ _ h1 h2)) T fun c c' hne => hs _ _ hne
  have hdT' : (T.map (starRingEnd ℂ)).det = (starRingEnd ℂ) T.det := by
    rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdT', hdT,
    map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_subtype (p := p) (Finset.univ.filter p) (by simp), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have := Complex.mul_conj' (S c c)
  simp only [hT, Matrix.submatrix_apply]
  push_cast
  rw [← this]
  ring
end GlobalTheory.TriSqrt
