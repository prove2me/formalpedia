-- Prove2me | solution 1 for KSPolySign.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:39:41.16738+00:00
-- url     : https://prove2.me/submissions/fa7c6726-3b02-4234-af68-7b7ee9a2d632

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign.L48
open KSPolySign

theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  open scoped MatrixOrder in
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.mul_assoc, trace_mul_comm]
  rw [Matrix.mul_assoc]
  have := (hB.mul_mul_conjTranspose_same S)
  simp only [star_eq_conjTranspose] at *
  rw [← Matrix.mul_assoc]
  exact this.trace_nonneg

theorem exists_vecMulVec_of_rank_le_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    ∃ a b : Fin n → ℂ, C = vecMulVec a b := by
  classical
  have h' : Module.finrank ℂ (LinearMap.range C.mulVecLin) ≤ 1 := h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h'
  have hcol : ∀ j : Fin n, ∃ c : ℂ, c • (v : Fin n → ℂ) = C *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := hv ⟨C *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose c hc using hcol
  refine ⟨v, c, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp [mulVec_single] at this
  simp [vecMulVec_apply, ← this, mul_comm]

theorem sandwich_of_rank_le_one {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    C * D * C = (C * D).trace • C := by
  obtain ⟨a, b, rfl⟩ := exists_vecMulVec_of_rank_le_one C h
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, trace, diag, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- trace of a product of two Hermitian matrices is real. -/
theorem trace_mul_star_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : star (A * B).trace = (A * B).trace := by
  rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm]

theorem im_eq_zero_of_star_eq {z : ℂ} (h : star z = z) : z.im = 0 := by
  have := congrArg Complex.im h
  simp at this; linarith

theorem frob_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∑ j, ∑ l, ‖X j l‖ ^ 2 = (X * X).trace.re := by
  conv_rhs => rw [show X * X = X * Xᴴ by rw [hX.eq]]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact (Complex.ofReal_re _).symm

theorem key_term {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) (hr : C.rank ≤ 1)
    (hD : D.IsHermitian) : ((C * D).trace.re) ^ 2 ≤ (D * D * (C * C)).trace.re := by
  set t := (C * D).trace with ht_def
  set c := C.trace with hc_def
  have ht : star t = t := trace_mul_star_eq hC.isHermitian hD
  have hcs : star c = c := by rw [hc_def, ← trace_conjTranspose, hC.isHermitian.eq]
  have hCC : C * C = c • C := by
    have := sandwich_of_rank_le_one C 1 hr
    simpa using this
  have hCDC : C * D * C = t • C := sandwich_of_rank_le_one C D hr
  by_cases hc0 : c = 0
  · have : C = 0 := (hC.trace_eq_zero_iff).mp hc0
    subst this; rw [ht_def]; simp
  let X := c • (D * C) - t • C
  have hXH : Xᴴ = c • (C * D) - t • C := by
    simp only [X, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, hD.eq,
      hC.isHermitian.eq, hcs, ht]
  have hpos : 0 ≤ (Xᴴ * X).trace := (posSemidef_conjTranspose_mul_self X).trace_nonneg
  have hexp : Xᴴ * X = (c * c) • (C * (D * D) * C) - (c * t * t) • C := by
    rw [hXH]
    simp only [X, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have e1 : C * D * (D * C) = C * (D * D) * C := by simp only [Matrix.mul_assoc]
    have e2 : C * D * C = t • C := hCDC
    have e3 : C * (D * C) = t • C := by rw [← Matrix.mul_assoc, hCDC]
    rw [e1, e2, e3, hCC]
    simp only [smul_smul]
    module
  rw [hexp, trace_sub, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at hpos
  have hcyc : (C * (D * D) * C).trace = (D * D * (C * C)).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm]
  rw [hcyc, ← hc_def] at hpos
  have hcre : c = (c.re : ℂ) := Complex.ext rfl (by simp [im_eq_zero_of_star_eq hcs])
  have htre : t = (t.re : ℂ) := Complex.ext rfl (by simp [im_eq_zero_of_star_eq ht])
  have hcpos : 0 < c.re := by
    have h0 := hC.trace_nonneg
    rw [← hc_def, Complex.nonneg_iff] at h0
    rcases h0.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hc0; rw [hcre, ← h]; simp
  set T := (D * D * (C * C)).trace
  have hpos' := (Complex.nonneg_iff.mp hpos).1
  rw [hcre, htre] at hpos'
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, zero_mul, Complex.mul_im, add_zero] at hpos'
  have e : c.re * c.re * T.re - c.re * t.re * t.re * c.re = (c.re * c.re) * (T.re - t.re ^ 2) := by
    ring
  rw [e] at hpos'
  have h2 := (mul_nonneg_iff_of_pos_left (by positivity)).mp hpos'
  linarith


theorem opNorm_le_frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    AgnosticTNS.opNorm M ≤ Real.sqrt (∑ j, ∑ l, ‖M j l‖ ^ 2) := by
  unfold AgnosticTNS.opNorm
  apply csSup_le
  · exact ⟨_, ⟨0, by simp, rfl⟩⟩
  rintro r ⟨x, hx, rfl⟩
  simp only [Set.mem_setOf_eq] at hx
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have h1 : ‖(M *ᵥ x) j‖ ≤ ∑ l, ‖M j l‖ * ‖x l‖ := by
    simp only [mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖M j l‖) (fun l => ‖x l‖)
  have h3 : 0 ≤ ∑ l, ‖M j l‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  calc ‖(M *ᵥ x) j‖ ^ 2 ≤ (∑ l, ‖M j l‖ * ‖x l‖) ^ 2 := by
        gcongr
    _ ≤ (∑ l, ‖M j l‖ ^ 2) * ∑ l, ‖x l‖ ^ 2 := h2
    _ ≤ (∑ l, ‖M j l‖ ^ 2) * 1 := by gcongr
    _ = ∑ l, ‖M j l‖ ^ 2 := mul_one _

theorem lemma_4_8 (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).PosSemidef ∧ (C i).rank ≤ 1) (hsq : (1 - ∑ i, C i * C i).PosSemidef) :
    (∀ D : Matrix (Fin n) (Fin n) ℂ, D.IsHermitian →
      ∑ i, ((C i * D).trace.re) ^ 2 ≤ (D * D * ∑ i, C i * C i).trace.re ∧
        (D * D * ∑ i, C i * C i).trace.re ≤ ∑ j, ∑ l, ‖D j l‖ ^ 2) ∧
    ∀ r : Fin k → ℝ,
      AgnosticTNS.opNorm (∑ i, ((r i : ℝ) : ℂ) • C i) ≤ Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ∧
        Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ≤ Real.sqrt (∑ i, r i ^ 2) := by
  have partA : ∀ D : Matrix (Fin n) (Fin n) ℂ, D.IsHermitian →
      ∑ i, ((C i * D).trace.re) ^ 2 ≤ (D * D * ∑ i, C i * C i).trace.re ∧
        (D * D * ∑ i, C i * C i).trace.re ≤ ∑ j, ∑ l, ‖D j l‖ ^ 2 := by
    intro D hD
    constructor
    · rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
      exact Finset.sum_le_sum fun i _ => key_term (C i) D (hC i).1 (hC i).2 hD
    · rw [frob_eq_trace D hD]
      have hDD : (D * D).PosSemidef := by
        have := posSemidef_conjTranspose_mul_self D
        rwa [hD.eq] at this
      have := trace_mul_nonneg_of_posSemidef hsq hDD
      rw [trace_mul_comm, Matrix.mul_sub, Matrix.mul_one, trace_sub] at this
      have := (Complex.nonneg_iff.mp this).1
      simp only [Complex.sub_re] at this
      linarith
  refine ⟨partA, fun r => ⟨opNorm_le_frob _, ?_⟩⟩
  set X := ∑ i, ((r i : ℝ) : ℂ) • C i with hX_def
  have hXH : X.IsHermitian := by
    unfold IsHermitian
    rw [hX_def, conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_smul, (hC i).1.isHermitian.eq]
    simp
  rw [frob_eq_trace X hXH]
  set f := (X * X).trace.re with hf
  have hf0 : 0 ≤ f := by
    rw [hf, ← frob_eq_trace X hXH]; positivity
  have htr : f = ∑ i, r i * (C i * X).trace.re := by
    rw [hf]
    conv_lhs => rw [hX_def]
    rw [Matrix.sum_mul, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hA := (partA X hXH)
  have hb : ∑ i, ((C i * X).trace.re) ^ 2 ≤ f := by
    rw [hf, ← frob_eq_trace X hXH]; exact hA.1.trans hA.2
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ r (fun i => (C i * X).trace.re)
  have h1 : f ≤ Real.sqrt (∑ i, r i ^ 2) * Real.sqrt f := by
    rw [htr] at hb ⊢
    refine hcs.trans ?_
    gcongr
  have hsf : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0
  have hR := Real.sqrt_nonneg (∑ i, r i ^ 2)
  have hs0 := Real.sqrt_nonneg f
  nlinarith

end KSPolySign.L48

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).PosSemidef ∧ (C i).rank ≤ 1) (hsq : (1 - ∑ i, C i * C i).PosSemidef) :
    (∀ D : Matrix (Fin n) (Fin n) ℂ, D.IsHermitian →
      ∑ i, ((C i * D).trace.re) ^ 2 ≤ (D * D * ∑ i, C i * C i).trace.re ∧
        (D * D * ∑ i, C i * C i).trace.re ≤ ∑ j, ∑ l, ‖D j l‖ ^ 2) ∧
    ∀ r : Fin k → ℝ,
      AgnosticTNS.opNorm (∑ i, ((r i : ℝ) : ℂ) • C i) ≤ Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ∧
        Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ≤ Real.sqrt (∑ i, r i ^ 2) := by
  apply KSPolySign.L48.lemma_4_8 <;> assumption
