-- Prove2me | solution 1 for NovyPQZK.Main.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T10:25:24.44468+00:00
-- url     : https://prove2.me/submissions/989ac81d-0f04-4366-9981-25227d054d84

import Mathlib
import Definitions.Def_NovyPQZK_Main_Fidelity

open scoped ComplexOrder Matrix
namespace NovyPQZK.Main

lemma zz (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [Complex.mul_re]

lemma zz' (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [mul_comm]; exact zz z

lemma tr_cs {ι : Type*} [Fintype ι] (S T : Matrix ι ι ℂ) :
    ‖(S * T).trace‖ ≤ √((S * Sᴴ).trace.re) * √((Tᴴ * T).trace.re) := by
  have h1 : (S * T).trace = ∑ p : ι × ι, S p.1 p.2 * T p.2 p.1 := by
    simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  have h2 : (S * Sᴴ).trace.re = ∑ p : ι × ι, ‖S p.1 p.2‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact zz _
  have h3 : (Tᴴ * T).trace.re = ∑ p : ι × ι, ‖T p.2 p.1‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact zz' _
  rw [h1, h2, h3]
  calc _ ≤ ∑ p : ι × ι, ‖S p.1 p.2 * T p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : ι × ι, ‖S p.1 p.2‖ * ‖T p.2 p.1‖ := by simp
    _ ≤ _ := by
      have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
        (fun p => ‖S p.1 p.2‖) (fun p => ‖T p.2 p.1‖)
      simpa using this

lemma psdSqrt_herm {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (psdSqrt A).IsHermitian ∧ psdSqrt A * psdSqrt A = A := by
  have h := hA.1
  unfold psdSqrt
  rw [dif_pos h]
  set U : Matrix ι ι ℂ := (h.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem h.eigenvectorUnitary.2
  have hspec := h.spectral_theorem
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    have e : (star fun i : ι => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) =
        fun i : ι => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ) := by ext i; simp
    simp [Matrix.star_eq_conjTranspose, mul_assoc, e]
  · have : (U * Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) * star U) *
        (U * Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) * star U)
        = U * (Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ))) * star U := by
      calc _ = U * Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) *
          (star U * U) * Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ))
            * star U := by simp only [mul_assoc]
        _ = _ := by rw [hUU]; simp only [mul_assoc, mul_one]
    rw [this, Matrix.diagonal_mul_diagonal]
    conv_rhs => rw [hspec]
    congr 3
    ext i : 1
    have := hA.eigenvalues_nonneg i
    simp [← Complex.ofReal_mul, Real.mul_self_sqrt this]

lemma trace_psdSqrt {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : M.IsHermitian) :
    (psdSqrt M).trace = ∑ i, ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ) := by
  unfold psdSqrt
  rw [dif_pos h]
  have hUU : star (h.eigenvectorUnitary : Matrix ι ι ℂ) * (h.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.star_mul_self_of_mem h.eigenvectorUnitary.2
  rw [Matrix.trace_mul_comm, ← mul_assoc, hUU]
  simp [Matrix.trace_diagonal]



lemma tr_NQ {ι : Type*} [Fintype ι] [DecidableEq ι] (N Q : Matrix ι ι ℂ) (hN : N.PosSemidef)
    (hQh : Qᴴ = Q) (hQ : Q * Q = Q) : (N * Q).trace.re ≤ N.trace.re := by
  have h1 : ((1 - Q)ᴴ * N * (1 - Q)).PosSemidef := hN.conjTranspose_mul_mul_same _
  have h2 : ((1 - Q)ᴴ * N * (1 - Q)).trace = N.trace - (N * Q).trace := by
    have e : (1 - Q)ᴴ * N * (1 - Q) = (1 - Q) * N * (1 - Q) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQh]
    have e2 : (1 - Q) * (1 - Q) = 1 - Q := by
      rw [sub_mul, mul_sub, mul_sub, hQ]; simp
    rw [e, Matrix.trace_mul_comm, ← mul_assoc, e2, sub_mul, one_mul, Matrix.trace_sub,
      Matrix.trace_mul_comm Q N]
  have h3 := h1.trace_nonneg
  rw [h2] at h3
  have := (Complex.nonneg_iff.mp h3).1
  simp at this
  linarith

lemma half {ι : Type} [Fintype ι] [DecidableEq ι] (A B P U W ρ σ : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (hA : A.IsHermitian) (hP : P.IsHermitian) (hPP : P * P = P)
    (hAA : A * A = ρ) (hBB : B * B = σ) (hUU : Uᴴ * U = 1)
    (hQ : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ) :
    ((U * Wᴴ * B * P * A).trace).re ≤ √((P * σ).trace.re) * √((P * ρ).trace.re) := by
  have hBh : Bᴴ = B := hB
  have hAh : Aᴴ = A := hA
  have hPh : Pᴴ = P := hP
  have e1 : U * Wᴴ * B * P * A = (U * Wᴴ * B * P) * (P * A) := by
    have : U * Wᴴ * B * P * A = U * Wᴴ * B * (P * P) * A := by rw [hPP]
    rw [this]; simp only [mul_assoc]
  have hcs := tr_cs (U * Wᴴ * B * P) (P * A)
  have hS : ((U * Wᴴ * B * P) * (U * Wᴴ * B * P)ᴴ).trace = (B * P * B * (W * Wᴴ)).trace := by
    have : (U * Wᴴ * B * P) * (U * Wᴴ * B * P)ᴴ = U * (Wᴴ * (B * P * B) * W) * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hBh, hPh]
      calc _ = U * Wᴴ * B * (P * P) * B * W * Uᴴ := by simp only [mul_assoc]
        _ = _ := by rw [hPP]; simp only [mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, hUU, one_mul,
      Matrix.trace_mul_comm (Wᴴ * (B * P * B)) W, ← mul_assoc, Matrix.trace_mul_comm]
  have hT : ((P * A)ᴴ * (P * A)).trace = (P * ρ).trace := by
    have : (P * A)ᴴ * (P * A) = A * P * A := by
      rw [Matrix.conjTranspose_mul, hAh, hPh]
      calc _ = A * (P * P) * A := by simp only [mul_assoc]
        _ = _ := by rw [hPP]
    rw [this, Matrix.trace_mul_comm (A * P) A, ← mul_assoc, hAA, Matrix.trace_mul_comm]
  have hN : (B * P * B).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (P * B)
    have e : (P * B)ᴴ * (P * B) = B * P * B := by
      rw [Matrix.conjTranspose_mul, hBh, hPh]
      calc _ = B * (P * P) * B := by simp only [mul_assoc]
        _ = _ := by rw [hPP]
    rwa [e] at this
  have hQh : (W * Wᴴ)ᴴ = W * Wᴴ := by simp
  have hNQ := tr_NQ _ _ hN hQh hQ
  have hNt : (B * P * B).trace = (P * σ).trace := by
    rw [Matrix.trace_mul_comm (B * P) B, ← mul_assoc, hBB, Matrix.trace_mul_comm]
  rw [e1]
  rw [hS, hT] at hcs
  rw [hNt] at hNQ
  calc _ ≤ ‖((U * Wᴴ * B * P) * (P * A)).trace‖ := Complex.re_le_norm _
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hNQ) (Real.sqrt_nonneg _)

lemma scal (l : ℝ) (hl : 0 ≤ l) :
    ((Real.sqrt l : ℝ) : ℂ)⁻¹ * (l : ℂ) = ((Real.sqrt l : ℝ) : ℂ) ∧
    ((Real.sqrt l : ℝ) : ℂ)⁻¹ * (((Real.sqrt l : ℝ) : ℂ)⁻¹ * (l : ℂ) * ((Real.sqrt l : ℝ) : ℂ)⁻¹)
      = ((Real.sqrt l : ℝ) : ℂ)⁻¹ := by
  by_cases h0 : l = 0
  · subst h0; simp
  · have ht : ((Real.sqrt l : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (lt_of_le_of_ne hl (Ne.symm h0))).ne'
    have : (l : ℂ) = ((Real.sqrt l : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hl]
    rw [this]
    constructor <;> field_simp

lemma tr_proj_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (P ρ : Matrix ι ι ℂ)
    (hP : IsProjector P) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  obtain ⟨hAh, hAA⟩ := psdSqrt_herm ρ hρ
  have hAh' : (psdSqrt ρ)ᴴ = psdSqrt ρ := hAh
  have hPh : Pᴴ = P := hP.1
  have h := (Matrix.posSemidef_conjTranspose_mul_self (P * psdSqrt ρ)).trace_nonneg
  have : ((P * psdSqrt ρ)ᴴ * (P * psdSqrt ρ)).trace = (P * ρ).trace := by
    have e : (P * psdSqrt ρ)ᴴ * (P * psdSqrt ρ) = psdSqrt ρ * P * psdSqrt ρ := by
      rw [Matrix.conjTranspose_mul, hAh', hPh]
      calc _ = psdSqrt ρ * (P * P) * psdSqrt ρ := by simp only [mul_assoc]
        _ = _ := by rw [hP.2]
    rw [e, Matrix.trace_mul_comm (psdSqrt ρ * P) (psdSqrt ρ), ← mul_assoc, hAA,
      Matrix.trace_mul_comm]
  rw [this] at h
  exact (Complex.nonneg_iff.mp h).1

lemma core {ι : Type} [Fintype ι] [DecidableEq ι] (P ρ σ : Matrix ι ι ℂ)
    (hP : IsProjector P) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    0 ≤ fidelity ρ σ ∧ fidelity ρ σ ≤ √((P * σ).trace.re) * √((P * ρ).trace.re) +
      √(1 - (P * σ).trace.re) * √(1 - (P * ρ).trace.re) := by
  obtain ⟨hAh, hAA⟩ := psdSqrt_herm ρ hρ.1
  obtain ⟨hBh, hBB⟩ := psdSqrt_herm σ hσ.1
  have hAh' : (psdSqrt ρ)ᴴ = psdSqrt ρ := hAh
  have hBh' : (psdSqrt σ)ᴴ = psdSqrt σ := hBh
  obtain ⟨A, hAd⟩ : ∃ A, A = psdSqrt ρ := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = psdSqrt σ := ⟨_, rfl⟩
  rw [← hAd] at hAh hAA hAh'
  rw [← hBd] at hBh hBB hBh'
  obtain ⟨X, hXd⟩ : ∃ X, X = B * A := ⟨_, rfl⟩
  have hMeq : psdSqrt ρ * σ * psdSqrt ρ = Xᴴ * X := by
    rw [← hAd, hXd, Matrix.conjTranspose_mul, hAh', hBh', ← hBB]
    simp only [mul_assoc]
  have hM : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hH := hM.1
  have hF : fidelity ρ σ = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    unfold fidelity
    rw [hMeq, trace_psdSqrt _ hH, Complex.re_sum]
    simp
  obtain ⟨U, hUd⟩ : ∃ U, U = (hH.eigenvectorUnitary : Matrix ι ι ℂ) := ⟨_, rfl⟩
  have hUU : Uᴴ * U = 1 := by
    rw [hUd]; exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hUU' : U * Uᴴ = 1 := by
    rw [hUd]; exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hspec : Xᴴ * X = U * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [hUd]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
    exact this
  obtain ⟨D, hDd⟩ : ∃ D, D = Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hYY : (X * U)ᴴ * (X * U) = D := by
    rw [Matrix.conjTranspose_mul]
    calc _ = Uᴴ * (Xᴴ * X) * U := by simp only [mul_assoc]
      _ = (Uᴴ * U) * D * (Uᴴ * U) := by rw [hspec, hDd]; simp only [mul_assoc]
      _ = D := by rw [hUU]; simp
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hM.eigenvalues_nonneg i
  obtain ⟨tinv, htd⟩ : ∃ tinv : ι → ℂ, tinv = fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)⁻¹ :=
    ⟨_, rfl⟩
  have htinv : star tinv = tinv := by
    ext i; simp [htd]
  obtain ⟨W, hWd⟩ : ∃ W, W = X * U * Matrix.diagonal tinv := ⟨_, rfl⟩
  have hWh : Wᴴ = Matrix.diagonal tinv * (X * U)ᴴ := by
    rw [hWd, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, htinv]
  have hWY : Wᴴ * (X * U) = Matrix.diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) := by
    rw [hWh, Matrix.mul_assoc (Matrix.diagonal tinv) ((X * U)ᴴ) (X * U), hYY, hDd, Matrix.diagonal_mul_diagonal]
    congr 1; ext i; simp only [htd]; exact (scal _ (hnn i)).1
  obtain ⟨e, hed⟩ : ∃ e : ι → ℂ, e = fun i => tinv i * ((hH.eigenvalues i : ℝ) : ℂ) * tinv i :=
    ⟨_, rfl⟩
  have hWW : Wᴴ * W = Matrix.diagonal e := by
    rw [hWh, hWd]
    calc _ = Matrix.diagonal tinv * ((X * U)ᴴ * (X * U)) * Matrix.diagonal tinv := by
          simp only [mul_assoc]
      _ = _ := by
        rw [hYY, hDd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hed]
  have hWe : W * Matrix.diagonal e = W := by
    rw [hWd, mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2; ext i; simp only [htd, hed]; exact (scal _ (hnn i)).2
  have hQ : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
    calc _ = W * (Wᴴ * W) * Wᴴ := by simp only [mul_assoc]
      _ = _ := by rw [hWW, hWe]
  have hfid : (fidelity ρ σ : ℂ) = (U * Wᴴ * B * P * A).trace + (U * Wᴴ * B * (1 - P) * A).trace := by
    have h1 : (fidelity ρ σ : ℂ) = (Matrix.diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))).trace := by
      rw [hF, Matrix.trace_diagonal]; push_cast; rfl
    rw [h1, ← hWY, hXd, ← Matrix.trace_add]
    have e : Wᴴ * (B * A * U) = (Wᴴ * B * A) * U := by simp only [mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have hP1 : IsProjector (1 - P) := by
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1.eq]
    · rw [sub_mul, mul_sub, mul_sub, hP.2]; simp
  have h1 := half A B P U W ρ σ hBh hAh hP.1 hP.2 hAA hBB hUU hQ
  have h2 := half A B (1 - P) U W ρ σ hBh hAh hP1.1 hP1.2 hAA hBB hUU hQ
  have ea : ((1 - P) * ρ).trace.re = 1 - (P * ρ).trace.re := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hρ.2]; simp
  have eb : ((1 - P) * σ).trace.re = 1 - (P * σ).trace.re := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hσ.2]; simp
  rw [ea, eb] at h2
  have hre : fidelity ρ σ = ((U * Wᴴ * B * P * A).trace).re + ((U * Wᴴ * B * (1 - P) * A).trace).re := by
    have := congrArg Complex.re hfid
    simpa using this
  refine ⟨?_, ?_⟩
  · rw [hF]; exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  · rw [hre]; linarith

lemma alg (x y p q : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : x^2 + p^2 = 1) (h2 : y^2 + q^2 = 1) : (x - y)^2 ≤ (x*q - p*y)^2 := by
  nlinarith [mul_nonneg hx hy, mul_nonneg hp hq, mul_nonneg hx hp, mul_nonneg hy hq, sq_nonneg (x-y),
    sq_nonneg (p-q), mul_nonneg (mul_nonneg hx hy) (mul_nonneg hp hq)]

theorem lemma_2' {ι : Type} [Fintype ι] [DecidableEq ι] (P ρ σ : Matrix ι ι ℂ)
    (hP : IsProjector P) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    |Real.sqrt (P * ρ).trace.re - Real.sqrt (P * σ).trace.re| ≤ purifiedDist ρ σ := by
  obtain ⟨hF0, hF⟩ := core P ρ σ hP hρ hσ
  have ha0 := tr_proj_nonneg P ρ hP hρ.1
  have hb0 := tr_proj_nonneg P σ hP hσ.1
  have hP1 : IsProjector (1 - P) := by
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1.eq]
    · rw [sub_mul, mul_sub, mul_sub, hP.2]; simp
  have ha1 := tr_proj_nonneg (1 - P) ρ hP1 hρ.1
  have hb1 := tr_proj_nonneg (1 - P) σ hP1 hσ.1
  have ea : ((1 - P) * ρ).trace.re = 1 - (P * ρ).trace.re := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hρ.2]; simp
  have eb : ((1 - P) * σ).trace.re = 1 - (P * σ).trace.re := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hσ.2]; simp
  rw [ea] at ha1
  rw [eb] at hb1
  set a := (P * ρ).trace.re
  set b := (P * σ).trace.re
  have hx := Real.sq_sqrt ha0
  have hy := Real.sq_sqrt hb0
  have hp := Real.sq_sqrt ha1
  have hq := Real.sq_sqrt hb1
  have key := alg (√a) (√b) (√(1 - a)) (√(1 - b)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by rw [hx, hp]; ring) (by rw [hy, hq]; ring)
  have hG : fidelity ρ σ ^ 2 ≤ (√b * √a + √(1 - b) * √(1 - a)) ^ 2 :=
    pow_le_pow_left₀ hF0 hF 2
  have hid : 1 - (√b * √a + √(1 - b) * √(1 - a)) ^ 2 = (√a * √(1 - b) - √(1 - a) * √b) ^ 2 := by
    have e1 : √b ^ 2 = b := hy
    have e2 : √a ^ 2 = a := hx
    have e3 : √(1 - b) ^ 2 = 1 - b := hq
    have e4 : √(1 - a) ^ 2 = 1 - a := hp
    nlinarith [e1, e2, e3, e4]
  unfold purifiedDist
  apply Real.abs_le_sqrt
  nlinarith [key, hid, hG]

end NovyPQZK.Main

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (P ρ σ : Matrix ι ι ℂ)
    (hP : NovyPQZK.Main.IsProjector P) (hρ : NovyPQZK.Main.IsDensity ρ) (hσ : NovyPQZK.Main.IsDensity σ) :
    |Real.sqrt (P * ρ).trace.re - Real.sqrt (P * σ).trace.re| ≤ NovyPQZK.Main.purifiedDist ρ σ :=
  NovyPQZK.Main.lemma_2' P ρ σ hP hρ hσ
