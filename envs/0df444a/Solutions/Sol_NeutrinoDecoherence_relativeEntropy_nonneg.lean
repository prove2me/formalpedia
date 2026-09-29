-- Prove2me | solution 1 for NeutrinoDecoherence.relativeEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:45:11.450168+00:00
-- url     : https://prove2.me/submissions/e2c46837-a1a4-401b-b440-bb1f80b6037c

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

theorem nd_gibbs {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log p - p * Real.log q - p + q ∧
      (p * Real.log p - p * Real.log q - p + q = 0 → p = q) := by
  rcases hp.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨by simp; linarith, fun h => ?_⟩
    simp at h
    linarith
  · have hx : 0 < q / p := div_pos hq hpos
    have hlog : Real.log (q / p) = Real.log q - Real.log p := Real.log_div hq.ne' hpos.ne'
    have key : p * Real.log (q / p) = p * Real.log q - p * Real.log p := by rw [hlog]; ring
    have hdiv : p * (q / p) = q := by field_simp
    refine ⟨?_, fun h => ?_⟩
    · have h1 := Real.log_le_sub_one_of_pos hx
      have h2 : p * Real.log (q / p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 hpos.le
      rw [key, mul_sub, hdiv, mul_one] at h2
      linarith
    · by_contra hne
      have hne' : q / p ≠ 1 := by
        intro h1
        rw [div_eq_one_iff_eq hpos.ne'] at h1
        exact hne h1.symm
      have h1 := Real.log_lt_sub_one_of_pos hx hne'
      have h2 : p * Real.log (q / p) < p * (q / p - 1) := mul_lt_mul_of_pos_left h1 hpos
      rw [key, mul_sub, hdiv, mul_one] at h2
      linarith

open Matrix in
theorem nd_tr4 {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) (a b : n → ℂ) :
    (U * diagonal a * star U * (V * diagonal b * star V)).trace =
      ∑ i, ∑ j, a i * b j * ((star U * V) i j * star ((star U * V) i j)) := by
  have h1 : U * diagonal a * star U * (V * diagonal b * star V) =
      U * (diagonal a * star U * V * diagonal b * star V) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : diagonal a * star U * V * diagonal b * star V * U =
      diagonal a * (star U * V) * diagonal b * star (star U * V) := by
    simp only [star_mul, star_star, Matrix.mul_assoc]
  rw [h2]
  generalize star U * V = W
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  ring

open Matrix in
theorem nd_spec {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

open Matrix in
theorem nd_rowsum {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M => (M i i).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
    Complex.re_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

open Matrix in
theorem nd_colsum {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (hW : star W * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M => (M j j).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
    Complex.re_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

open NeutrinoDecoherence Matrix ComplexOrder in
theorem solution {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hσpos : σ.PosDef) :
    0 ≤ relativeEntropy ρ σ ∧ (relativeEntropy ρ σ = 0 ↔ ρ = σ) := by
  obtain ⟨hρpsd, hρtr⟩ := hρ
  obtain ⟨hσpsd, hσtr⟩ := hσ
  have hA : ρ.IsHermitian := hρpsd.1
  have hB : σ.IsHermitian := hσpsd.1
  have hρsa : IsSelfAdjoint ρ := hA.isSelfAdjoint
  have hpn : ∀ i, 0 ≤ hA.eigenvalues i := hρpsd.eigenvalues_nonneg
  have hqp : ∀ j, 0 < hB.eigenvalues j := hσpos.eigenvalues_pos
  have hps : ∑ i, hA.eigenvalues i = 1 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [hρtr] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at h2
    exact h2.symm
  have hqs : ∑ j, hB.eigenvalues j = 1 := by
    have h := hB.trace_eq_sum_eigenvalues
    rw [hσtr] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at h2
    exact h2.symm
  have hρs : ρ = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    have h := nd_spec ρ hA (fun x => x)
    rw [cfc_id' (R := ℝ) (a := ρ)] at h
    exact h
  have hσs : σ = (hB.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ)) *
      star (hB.eigenvectorUnitary : Matrix n n ℂ) := by
    have hσsa : IsSelfAdjoint σ := hB.isSelfAdjoint
    have h := nd_spec σ hB (fun x => x)
    rw [cfc_id' (R := ℝ) (a := σ)] at h
    exact h
  have hlogρ := nd_spec ρ hA Real.log
  have hlogσ := nd_spec σ hB Real.log
  set p := hA.eigenvalues with hpdef
  set q := hB.eigenvalues with hqdef
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hV1 : star V * V = 1 := Unitary.coe_star_mul_self _
  have hV2 : V * star V = 1 := Unitary.coe_mul_star_self _
  have hW1 : (star U * V) * star (star U * V) = 1 := by
    rw [star_mul, star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV2, Matrix.mul_one, hU1]
  have hW2 : star (star U * V) * (star U * V) = 1 := by
    rw [star_mul, star_star]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hV1]
  have hrow := nd_rowsum (star U * V) hW1
  have hcol := nd_colsum (star U * V) hW2
  have t1 : (ρ * cfc Real.log ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [hlogρ]
    conv_lhs => rw [hρs]
    rw [nd_tr4 U U, hU1]
    simp [Matrix.one_apply, Complex.re_sum]
  have t2 : (ρ * cfc Real.log σ).trace.re =
      ∑ i, ∑ j, p i * Real.log (q j) * Complex.normSq ((star U * V) i j) := by
    rw [hlogσ]
    conv_lhs => rw [hρs]
    rw [nd_tr4 U V, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hS : relativeEntropy ρ σ = ∑ i, ∑ j, Complex.normSq ((star U * V) i j) *
      (p i * Real.log (p i) - p i * Real.log (q j) - p i + q j) := by
    unfold relativeEntropy
    rw [t1, t2]
    have e1 : ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * (p i * Real.log (p i)) =
        ∑ i, p i * Real.log (p i) :=
      Finset.sum_congr rfl (fun i _ => by rw [← Finset.sum_mul, hrow i, one_mul])
    have e2 : ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * p i = 1 := by
      rw [← hps]
      exact Finset.sum_congr rfl (fun i _ => by rw [← Finset.sum_mul, hrow i, one_mul])
    have e3 : ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * q j = 1 := by
      rw [Finset.sum_comm, ← hqs]
      exact Finset.sum_congr rfl (fun j _ => by rw [← Finset.sum_mul, hcol j, one_mul])
    have e4 : ∑ i, ∑ j, Complex.normSq ((star U * V) i j) *
          (p i * Real.log (p i) - p i * Real.log (q j) - p i + q j) =
        ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * (p i * Real.log (p i)) -
          ∑ i, ∑ j, p i * Real.log (q j) * Complex.normSq ((star U * V) i j) -
          ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * p i +
          ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * q j := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e4, e1, e2, e3]
    ring
  have hterm : ∀ i j, 0 ≤ Complex.normSq ((star U * V) i j) *
      (p i * Real.log (p i) - p i * Real.log (q j) - p i + q j) :=
    fun i j => mul_nonneg (Complex.normSq_nonneg _) (nd_gibbs (hpn i) (hqp j)).1
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))
  · constructor
    · intro h0
      rw [hS] at h0
      have hz : ∀ i j, Complex.normSq ((star U * V) i j) *
          (p i * Real.log (p i) - p i * Real.log (q j) - p i + q j) = 0 := by
        intro i j
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
          Finset.sum_nonneg (fun j _ => hterm i j))).mp h0 i (Finset.mem_univ i)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp h1 j (Finset.mem_univ j)
      have hcomm : (star U * V) * diagonal (fun j => ((q j : ℝ) : ℂ)) =
          diagonal (fun i => ((p i : ℝ) : ℂ)) * (star U * V) := by
        ext i j
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
        rcases mul_eq_zero.mp (hz i j) with h | h
        · rw [Complex.normSq_eq_zero.mp h]
          simp
        · rw [(nd_gibbs (hpn i) (hqp j)).2 h]
          ring
      calc ρ = U * diagonal (fun i => ((p i : ℝ) : ℂ)) * star U := hρs
        _ = U * diagonal (fun i => ((p i : ℝ) : ℂ)) *
            ((star U * V) * star (star U * V)) * star U := by rw [hW1, Matrix.mul_one]
        _ = U * (diagonal (fun i => ((p i : ℝ) : ℂ)) * (star U * V)) *
            star (star U * V) * star U := by simp only [Matrix.mul_assoc]
        _ = U * ((star U * V) * diagonal (fun j => ((q j : ℝ) : ℂ))) *
            star (star U * V) * star U := by rw [hcomm]
        _ = (U * star U) * V * diagonal (fun j => ((q j : ℝ) : ℂ)) *
            (star V * (U * star U)) := by simp only [star_mul, star_star, Matrix.mul_assoc]
        _ = σ := by rw [hU2, Matrix.one_mul, Matrix.mul_one, hσs]
    · intro h
      unfold relativeEntropy
      rw [h, sub_self]
