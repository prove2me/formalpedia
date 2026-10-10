-- Prove2me | solution 1 for IQCAlg.Main.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:42:23.474992+00:00
-- url     : https://prove2.me/submissions/59021097-10fd-46ae-9a8e-17647a12fc3a

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix
open scoped InnerProductSpace

namespace RRAux_IQCAlg_Main_theorem_4
theorem quad_expand {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ (P *ᵥ x) = ∑ i, hP.eigenvalues i * (⟪hP.eigenvectorBasis i, WithLp.toLp 2 x⟫_ℝ) ^ 2 ∧
    x ⬝ᵥ x = ∑ i, (⟪hP.eigenvectorBasis i, WithLp.toLp 2 x⟫_ℝ) ^ 2 := by
  set b := hP.eigenvectorBasis
  set X : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hdot : ∀ v : EuclideanSpace ℝ n, x ⬝ᵥ (v : n → ℝ) = ⟪v, X⟫_ℝ := by
    intro v
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [X, star_trivial]
  have hx : x = ∑ i, ⟪b i, X⟫_ℝ • ((b i : EuclideanSpace ℝ n) : n → ℝ) := by
    have h := b.sum_repr X
    have h2 := congrArg (fun v : EuclideanSpace ℝ n => (v : n → ℝ)) h
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, b.repr_apply_apply] at h2
    rw [h2]
  have hPx : P *ᵥ x = ∑ i, (⟪b i, X⟫_ℝ * hP.eigenvalues i) • ((b i : EuclideanSpace ℝ n) : n → ℝ) := by
    conv_lhs => rw [hx]
    rw [mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_smul, hP.mulVec_eigenvectorBasis, smul_smul]
  constructor
  · rw [hPx, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, hdot, smul_eq_mul, real_inner_comm]
    ring
  · conv_lhs => arg 2; rw [hx]
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, hdot, smul_eq_mul, real_inner_comm]
    ring

theorem rayleigh {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P.IsHermitian) (x : n → ℝ) :
    (⨅ i, hP.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) ∧
    x ⬝ᵥ (P *ᵥ x) ≤ (⨆ i, hP.eigenvalues i) * (x ⬝ᵥ x) := by
  obtain ⟨h1, h2⟩ := quad_expand P hP x
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (ciInf_le (Set.finite_range _).bddBelow i) (sq_nonneg _)
  · refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (le_ciSup (Set.finite_range _).bddAbove i) (sq_nonneg _)

theorem quad_transpose {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k m ℝ) (P : Matrix k k ℝ) (Y : Matrix k n ℝ) (u : m → ℝ) (w : n → ℝ) :
    u ⬝ᵥ ((Xᵀ * P * Y) *ᵥ w) = (X *ᵥ u) ⬝ᵥ (P *ᵥ (Y *ᵥ w)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

open IQCAlg.Main

theorem lmi_eval {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (lam ρ : ℝ)
    (x : Fin nξ ⊕ Fin nζ → ℝ) (w : Fin d → ℝ) :
    (Sum.elim x w) ⬝ᵥ (lmiMat A B C Ψ M P lam ρ *ᵥ Sum.elim x w)
      = qf P (Ahat A C Ψ *ᵥ x + Bhat B Ψ *ᵥ w) - ρ ^ 2 * qf P x
        + lam * qf M (Chat C Ψ *ᵥ x + Dhat Ψ *ᵥ w) := by
  unfold lmiMat qf
  rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, quad_transpose,
    fromCols_mulVec, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sub_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_sub, dotProduct_smul, quad_transpose, mulVec_add, add_dotProduct, smul_eq_mul]
  ring

theorem scale_step (c c1 ρ V1 V0 q lam : ℝ) (hc : 0 ≤ c) (hc1 : ρ ^ 2 * c1 = c)
    (h : V1 - ρ ^ 2 * V0 + lam * q ≤ 0) :
    ρ ^ 2 * (c1 * V1) - ρ ^ 2 * (c * V0) + lam * (c * q) ≤ 0 := by
  have h2 := mul_le_mul_of_nonneg_left h hc
  rw [← mul_assoc, hc1]
  nlinarith

theorem dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

end RRAux_IQCAlg_Main_theorem_4

open RRAux_IQCAlg_Main_theorem_4 in
open IQCAlg.Main in
theorem solution {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ) (hM : M.IsSymm)
    (φ : (ℕ → Fin d → ℝ) → (ℕ → Fin d → ℝ))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ξs : Fin nξ → ℝ) (ζs : Fin nζ → ℝ) (ys us : Fin d → ℝ) (zs : Fin nz → ℝ)
    (h38a : ξs = A *ᵥ ξs + B *ᵥ us) (h38b : ys = C *ᵥ ξs)
    (h38c : ζs = Ψ.AΨ *ᵥ ζs + Ψ.ByΨ *ᵥ ys + Ψ.BuΨ *ᵥ us)
    (h38d : zs = Ψ.CΨ *ᵥ ζs + Ψ.DyΨ *ᵥ ys + Ψ.DuΨ *ᵥ us)
    (hIQC : IsRhoHardIQC φ Ψ M ρ ys us ζs zs)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (hP : P.PosDef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hLMI : (-(lmiMat A B C Ψ M P lam ρ)).PosSemidef) :
    ∀ ξ : ℕ → Fin nξ → ℝ,
      (∀ k, ξ (k + 1) = A *ᵥ ξ k + B *ᵥ φ (fun j => C *ᵥ ξ j) k) →
      ∀ k, norm2 (ξ k - ξs) ≤ Real.sqrt (condNum P hP.isHermitian) * ρ ^ k * norm2 (ξ 0 - ξs) := by
  intro ξ hξ k
  set yq : ℕ → Fin d → ℝ := fun j => C *ᵥ ξ j with hyq
  set uq := φ yq with huq
  set ζ := psiState Ψ ζs yq uq with hζ
  set xv : ℕ → (Fin nξ ⊕ Fin nζ → ℝ) := fun j => Sum.elim (ξ j - ξs) (ζ j - ζs) with hxv
  set wv : ℕ → Fin d → ℝ := fun j => uq j - us with hwv
  have hstep : ∀ j, Ahat A C Ψ *ᵥ xv j + Bhat B Ψ *ᵥ wv j = xv (j + 1) := by
    intro j
    simp only [hxv, hwv, Ahat, Bhat, fromBlocks_mulVec, fromRows_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, zero_mulVec, add_zero, ← Sum.elim_add_add]
    congr 1
    · have e : A *ᵥ (ξ j - ξs) + B *ᵥ (uq j - us)
          = (A *ᵥ ξ j + B *ᵥ uq j) - (A *ᵥ ξs + B *ᵥ us) := by
        rw [mulVec_sub, mulVec_sub]; abel
      rw [e, ← h38a, hξ j]
    · have e : (Ψ.ByΨ * C) *ᵥ (ξ j - ξs) + Ψ.AΨ *ᵥ (ζ j - ζs) + Ψ.BuΨ *ᵥ (uq j - us)
          = (Ψ.AΨ *ᵥ ζ j + Ψ.ByΨ *ᵥ yq j + Ψ.BuΨ *ᵥ uq j)
            - (Ψ.AΨ *ᵥ ζs + Ψ.ByΨ *ᵥ ys + Ψ.BuΨ *ᵥ us) := by
        rw [h38b, ← mulVec_mulVec, mulVec_sub, mulVec_sub, mulVec_sub, mulVec_sub]
        simp only [hyq]; abel
      rw [e, ← h38c]
      rfl
  have hout : ∀ j, Chat C Ψ *ᵥ xv j + Dhat Ψ *ᵥ wv j = psiOut Ψ ζs yq uq j - zs := by
    intro j
    simp only [hxv, hwv, Chat, Dhat, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      psiOut]
    rw [h38d, h38b, ← mulVec_mulVec, mulVec_sub, mulVec_sub, mulVec_sub, mulVec_sub]
    simp only [hyq, hζ]; abel
  have hdiss : ∀ j, qf P (xv (j + 1)) - ρ ^ 2 * qf P (xv j)
      + lam * qf M (psiOut Ψ ζs yq uq j - zs) ≤ 0 := by
    intro j
    have h := hLMI.dotProduct_mulVec_nonneg (Sum.elim (xv j) (wv j))
    rw [star_trivial, neg_mulVec, dotProduct_neg, lmi_eval, hstep, hout] at h
    linarith
  set V : ℕ → ℝ := fun j => qf P (xv j) with hV
  set W : ℕ → ℝ := fun j => (ρ ^ (2 * j))⁻¹ * V j with hW
  set Q : ℕ → ℝ := fun j => (ρ ^ (2 * j))⁻¹ * qf M (psiOut Ψ ζs yq uq j - zs) with hQ
  have htel : ∀ k, ρ ^ 2 * W k + lam * ∑ j ∈ Finset.range k, Q j ≤ ρ ^ 2 * W 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add]
      have hc1 : ρ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹ = (ρ ^ (2 * k))⁻¹ := by
        have : ρ ^ (2 * (k + 1)) = ρ ^ (2 * k) * ρ ^ 2 := by ring
        rw [this, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
      have := scale_step (ρ ^ (2 * k))⁻¹ (ρ ^ (2 * (k + 1)))⁻¹ ρ (V (k + 1)) (V k)
        (qf M (psiOut Ψ ζs yq uq k - zs)) lam (by positivity) hc1 (hdiss k)
      simp only [hW, hQ]
      simp only [hW] at ih
      linarith
  have hsum : 0 ≤ lam * ∑ j ∈ Finset.range k, Q j := by
    apply mul_nonneg hlam
    rcases k with _ | k
    · simp
    · exact hIQC.2.2 yq k
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hWk : W k ≤ W 0 := by
    have := htel k
    have : ρ ^ 2 * W k ≤ ρ ^ 2 * W 0 := by linarith
    exact le_of_mul_le_mul_left this hρ2
  have hVk : V k ≤ ρ ^ (2 * k) * V 0 := by
    have hpos : 0 < ρ ^ (2 * k) := by positivity
    simp only [hW, pow_zero, mul_zero, inv_one, one_mul] at hWk
    rw [inv_mul_le_iff₀ hpos] at hWk
    exact hWk
  -- spectral bounds
  rcases Nat.eq_zero_or_pos nξ with h0 | hpos
  · subst h0
    have : ∀ v : Fin 0 → ℝ, norm2 v = 0 := fun v => by simp [norm2, dotProduct]
    rw [this, this]; simp
  have : Nonempty (Fin nξ ⊕ Fin nζ) := ⟨Sum.inl ⟨0, hpos⟩⟩
  set hH := hP.isHermitian
  set lmin := ⨅ i, hH.eigenvalues i with hlmin
  set lmax := ⨆ i, hH.eigenvalues i with hlmax
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := hH.eigenvalues)
  have hlmin_pos : 0 < lmin := by rw [hlmin, ← hi0]; exact hP.eigenvalues_pos i0
  have hle : lmin ≤ lmax := (ciInf_le (Set.finite_range _).bddBelow i0).trans
    (le_ciSup (Set.finite_range _).bddAbove i0)
  have hlmax_pos : 0 < lmax := lt_of_lt_of_le hlmin_pos hle
  obtain ⟨rk, -⟩ := rayleigh P hH (xv k)
  obtain ⟨-, r0⟩ := rayleigh P hH (xv 0)
  have hx0 : xv 0 ⬝ᵥ xv 0 = (ξ 0 - ξs) ⬝ᵥ (ξ 0 - ξs) := by
    simp only [hxv, sumElim_dotProduct_sumElim, hζ, psiState, sub_self, dotProduct_zero,
      add_zero]
  have hxk : (ξ k - ξs) ⬝ᵥ (ξ k - ξs) ≤ xv k ⬝ᵥ xv k := by
    simp only [hxv, sumElim_dotProduct_sumElim]
    linarith [dot_self_nonneg (ζ k - ζs)]
  set a := (ξ k - ξs) ⬝ᵥ (ξ k - ξs)
  set b := (ξ 0 - ξs) ⬝ᵥ (ξ 0 - ξs)
  have hb : 0 ≤ b := dot_self_nonneg _
  have hmain : lmin * a ≤ lmax * (ρ ^ (2 * k) * b) := by
    have h1 : lmin * a ≤ lmin * (xv k ⬝ᵥ xv k) := mul_le_mul_of_nonneg_left hxk hlmin_pos.le
    have rk' : lmin * (xv k ⬝ᵥ xv k) ≤ V k := rk
    have h2 : ρ ^ (2 * k) * V 0 ≤ ρ ^ (2 * k) * (lmax * b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hx0]; exact r0
    have e : ρ ^ (2 * k) * (lmax * b) = lmax * (ρ ^ (2 * k) * b) := by ring
    linarith
  have hcond : condNum P hP.isHermitian = lmax / lmin := rfl
  have hab : a ≤ lmax / lmin * ρ ^ (2 * k) * b := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlmin_pos]
    nlinarith
  unfold norm2
  rw [hcond]
  calc Real.sqrt a ≤ Real.sqrt (lmax / lmin * ρ ^ (2 * k) * b) := Real.sqrt_le_sqrt hab
    _ = Real.sqrt (lmax / lmin) * ρ ^ k * Real.sqrt b := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      congr 2
      rw [pow_mul, show (ρ ^ 2) ^ k = (ρ ^ k) ^ 2 by ring, Real.sqrt_sq (by positivity)]

#print axioms solution
