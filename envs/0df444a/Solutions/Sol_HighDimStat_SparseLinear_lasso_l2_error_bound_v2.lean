-- Prove2me | solution 1 for HighDimStat.SparseLinear.lasso_l2_error_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:58:52.176503+00:00
-- url     : https://prove2.me/submissions/5637bdf6-78de-4251-b25c-11fe9ea2b64a

/-
Wainwright, High-Dimensional Statistics, Theorem 7.13 (a): deterministic `ℓ₂` and `ℓ₁` error bounds
for the Lagrangian Lasso under the restricted eigenvalue condition RE(κ, 3).

Basic inequality (compare with `θ*`), `|⟨Xᵀw/n, ν⟩| ≤ (λ/2)‖ν‖₁` for `ν = θhat - θ*`, and
`‖θ*‖₁ - ‖θhat‖₁ ≤ ‖ν_S‖₁ - ‖ν_{Sᶜ}‖₁` give the cone condition `‖ν_{Sᶜ}‖₁ ≤ 3‖ν_S‖₁` and
`‖Xν‖²/n ≤ 3λ‖ν_S‖₁ ≤ 3λ√s‖ν‖₂`; RE then gives `κ‖ν‖₂ ≤ 3λ√s`.
-/
import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedEigenvalue
import Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm

set_option autoImplicit false

namespace LassoProof

open HighDimStat.SparseLinear

theorem l1S_le {d : ℕ} (S : Finset (Fin d)) (ν : Fin d → ℝ) :
    ∑ j ∈ S, |ν j| ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, ν j ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  calc (∑ j ∈ S, |ν j|) ^ 2 ≤ S.card * ∑ j ∈ S, |ν j| ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ S.card * ∑ j, ν j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc ∑ j ∈ S, |ν j| ^ 2 = ∑ j ∈ S, ν j ^ 2 := by simp [sq_abs]
        _ ≤ ∑ j, ν j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem sum_sq_sub {n : ℕ} (a b : Fin n → ℝ) :
    ∑ i, (a i - b i) ^ 2 = ∑ i, a i ^ 2 - 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
  have : ∀ i, (a i - b i) ^ 2 = a i ^ 2 - 2 * (a i * b i) + b i ^ 2 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem dot_eq {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) (ν : Fin d → ℝ) :
    ∑ i, w i * X.mulVec ν i = ∑ j, X.transpose.mulVec w j * ν j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

theorem l1_diff_le {d : ℕ} (S : Finset (Fin d)) (θstar θhat : Fin d → ℝ)
    (hS : HasSupport θstar S) :
    l1Norm θstar - l1Norm θhat ≤
      ∑ j ∈ S, |θhat j - θstar j| - ∑ j ∈ Sᶜ, |θhat j - θstar j| := by
  unfold l1Norm
  rw [← Finset.sum_add_sum_compl S (fun j => |θstar j|),
    ← Finset.sum_add_sum_compl S (fun j => |θhat j|)]
  have hc : ∑ j ∈ Sᶜ, |θstar j| = 0 :=
    Finset.sum_eq_zero (fun j hj => by simp [hS j (Finset.mem_compl.mp hj)])
  have hc2 : ∑ j ∈ Sᶜ, |θhat j - θstar j| = ∑ j ∈ Sᶜ, |θhat j| :=
    Finset.sum_congr rfl (fun j hj => by simp [hS j (Finset.mem_compl.mp hj)])
  have hs : ∑ j ∈ S, |θstar j| ≤ ∑ j ∈ S, |θhat j| + ∑ j ∈ S, |θhat j - θstar j| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    calc |θstar j| = |θhat j + (θstar j - θhat j)| := by ring_nf
      _ ≤ |θhat j| + |θstar j - θhat j| := abs_add_le _ _
      _ = |θhat j| + |θhat j - θstar j| := by rw [abs_sub_comm]
  linarith


theorem main_bound {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam_pos : 0 < lam)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat) :
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) := by
  classical
  set ν : Fin d → ℝ := fun j => θhat j - θstar j with hν
  have hνsub : ν = θhat - θstar := by funext j; rfl
  show Real.sqrt (∑ j, ν j ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm ν ≤ 4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, ν j ^ 2)
  have hR0 : 0 ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  have hr0 : 0 ≤ Real.sqrt (∑ j, ν j ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (∑ j, ν j ^ 2) ^ 2 = ∑ j, ν j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsumsq0 : 0 ≤ ∑ j, ν j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl1split : l1Norm ν = ∑ j ∈ S, |ν j| + ∑ j ∈ Sᶜ, |ν j| := by
    unfold l1Norm; exact (Finset.sum_add_sum_compl S (fun j => |ν j|)).symm
  have hS1 := l1S_le S ν
  have hC0 : ∀ j ∈ S, 0 ≤ |ν j| := fun _ _ => abs_nonneg _
  have hS1nn : 0 ≤ ∑ j ∈ S, |ν j| := Finset.sum_nonneg hC0
  have hC1nn : 0 ≤ ∑ j ∈ Sᶜ, |ν j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hn : n = 0
  · -- degenerate case: no observations
    subst hn
    have hθ : l1Norm θhat ≤ l1Norm (0 : Fin d → ℝ) := by
      have := hsol 0
      simp at this
      have h2 := (mul_le_mul_iff_of_pos_left hlam_pos).mp this
      simpa [l1Norm] using h2
    have hl0 : l1Norm (0 : Fin d → ℝ) = 0 := by simp [l1Norm]
    have hθz : ∀ j, θhat j = 0 := by
      intro j
      have hnn : ∀ k ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |θhat k| := fun _ _ => abs_nonneg _
      have h1 : ∑ k, |θhat k| = 0 := le_antisymm (by simpa [l1Norm, hl0] using hθ)
        (Finset.sum_nonneg hnn)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h1 j (Finset.mem_univ j)
      simpa using this
    have hcone : ConeSet S 3 ν := by
      unfold ConeSet
      have : ∑ j ∈ Sᶜ, |ν j| = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have h1 := hSupport j (Finset.mem_compl.mp hj)
        show |θhat j - θstar j| = 0
        rw [hθz j, h1]
        simp
      rw [this]
      positivity
    have hre := hRE ν hcone
    simp at hre
    have hsum0 : ∑ j, ν j ^ 2 ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith
    have hr : Real.sqrt (∑ j, ν j ^ 2) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos hsum0]
    have hνz : ∀ j, ν j = 0 := by
      intro j
      have h1 : ∑ k, ν k ^ 2 = 0 := le_antisymm hsum0 hsumsq0
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (ν k))).mp h1 j
        (Finset.mem_univ j)
      simpa using this
    refine ⟨?_, ?_⟩
    · rw [hr]
      exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hκ.le) hR0) hlam_pos.le
    · have : l1Norm ν = 0 := by
        unfold l1Norm
        exact Finset.sum_eq_zero (fun j _ => by rw [hνz j]; simp)
      rw [hr]
      simpa using this.le
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnl : 0 < (n : ℝ) * lam := mul_pos hnR hlam_pos
    -- the residual
    have hy : ∀ i, (X.mulVec θstar + w) i - X.mulVec θhat i = w i - X.mulVec ν i := by
      intro i
      have hm : X.mulVec ν = X.mulVec θhat - X.mulVec θstar := by
        rw [hνsub]; exact Matrix.mulVec_sub X θhat θstar
      simp [hm]
      ring
    have hb := hsol θstar
    have e1 : ∑ i, ((X.mulVec θstar + w) i - X.mulVec θhat i) ^ 2 =
        ∑ i, w i ^ 2 - 2 * ∑ i, w i * X.mulVec ν i + ∑ i, (X.mulVec ν i) ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [hy i])]
      exact sum_sq_sub _ _
    have e2 : ∑ i, ((X.mulVec θstar + w) i - X.mulVec θstar i) ^ 2 = ∑ i, w i ^ 2 := by
      simp
    rw [e1, e2] at hb
    set A := ∑ i, w i ^ 2 with hA
    set B := ∑ i, w i * X.mulVec ν i with hB
    set C := ∑ i, (X.mulVec ν i) ^ 2 with hC
    set H := l1Norm θhat with hH
    set T := l1Norm θstar with hT
    have hc : (1 / (2 * (n : ℝ))) * (2 * (n : ℝ)) = 1 := by field_simp
    have hbasic : C - 2 * B ≤ 2 * (n : ℝ) * lam * (T - H) := by
      have h1 : (1 / (2 * (n : ℝ))) * (C - 2 * B) ≤ lam * (T - H) := by
        calc (1 / (2 * (n : ℝ))) * (C - 2 * B)
            = ((1 / (2 * (n : ℝ))) * (A - 2 * B + C) + lam * H) -
              ((1 / (2 * (n : ℝ))) * A + lam * T) + lam * (T - H) := by ring
          _ ≤ lam * (T - H) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
      have h3 : 2 * (n : ℝ) * ((1 / (2 * (n : ℝ))) * (C - 2 * B)) = C - 2 * B := by
        field_simp
      linarith
    -- bound on the cross term
    have hg : ∀ j, |X.transpose.mulVec w j| ≤ (n : ℝ) * lam / 2 := by
      intro j
      have h1 : |X.transpose.mulVec w j / (n : ℝ)| ≤
          linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) :=
        le_ciSup (f := fun j => |X.transpose.mulVec w j / (n : ℝ)|) (Finite.bddAbove_range _) j
      rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR] at h1
      have hl2 : linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam / 2 := by linarith
      calc |X.transpose.mulVec w j| ≤ linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) * n := h1
        _ ≤ lam / 2 * n := mul_le_mul_of_nonneg_right hl2 hnR.le
        _ = (n : ℝ) * lam / 2 := by ring
    have hBle : |B| ≤ (n : ℝ) * lam / 2 * l1Norm ν := by
      rw [hB, dot_eq]
      calc |∑ j, X.transpose.mulVec w j * ν j| ≤ ∑ j, |X.transpose.mulVec w j * ν j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (n : ℝ) * lam / 2 * |ν j| := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hg j) (abs_nonneg _)
        _ = (n : ℝ) * lam / 2 * l1Norm ν := by
            unfold l1Norm; rw [Finset.mul_sum]
    have hdiff := l1_diff_le S θstar θhat hSupport
    set a := ∑ j ∈ S, |ν j| with ha
    set b := ∑ j ∈ Sᶜ, |ν j| with hb'
    have hdiff' : T - H ≤ a - b := hdiff
    have hCbound : C ≤ (n : ℝ) * lam * (3 * a - b) := by
      have h1 := abs_le.mp hBle
      have h2 : l1Norm ν = a + b := hl1split
      rw [h2] at h1
      have h3 : 2 * (n : ℝ) * lam * (T - H) ≤ 2 * (n : ℝ) * lam * (a - b) :=
        mul_le_mul_of_nonneg_left hdiff' (by positivity)
      linarith [h1.1, h1.2, hbasic, h3]
    have hC0' : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hcone_ab : b ≤ 3 * a := by
      have : 0 ≤ (n : ℝ) * lam * (3 * a - b) := le_trans hC0' hCbound
      have := (mul_nonneg_iff_of_pos_left hnl).mp this
      linarith
    have hcone : ConeSet S 3 ν := by
      unfold ConeSet; exact hcone_ab
    have hre := hRE ν hcone
    have hre' : κ * ∑ j, ν j ^ 2 ≤ C / (n : ℝ) := hre
    have hC3 : C / (n : ℝ) ≤ 3 * lam * a := by
      rw [div_le_iff₀ hnR]
      have hbn := mul_nonneg hnl.le hC1nn
      calc C ≤ (n : ℝ) * lam * (3 * a - b) := hCbound
        _ = 3 * lam * a * n - n * lam * b := by ring
        _ ≤ 3 * lam * a * n := by linarith
    have hmain : κ * Real.sqrt (∑ j, ν j ^ 2) ^ 2 ≤
        3 * lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, ν j ^ 2)) := by
      rw [hsq]
      calc κ * ∑ j, ν j ^ 2 ≤ C / (n : ℝ) := hre'
        _ ≤ 3 * lam * a := hC3
        _ ≤ 3 * lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, ν j ^ 2)) :=
            mul_le_mul_of_nonneg_left hS1 (by positivity)
    refine ⟨?_, ?_⟩
    · set r := Real.sqrt (∑ j, ν j ^ 2) with hr
      set R := Real.sqrt (S.card : ℝ) with hR
      by_cases hr0' : r = 0
      · rw [hr0']; positivity
      · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr0')
        have h1 : κ * r ≤ 3 * lam * R := by
          have : κ * r ^ 2 ≤ 3 * lam * (R * r) := hmain
          nlinarith
        calc r = (κ * r) / κ := by field_simp
          _ ≤ (3 * lam * R) / κ := div_le_div_of_nonneg_right h1 hκ.le
          _ = (3 / κ) * R * lam := by ring
    · have h2 : l1Norm ν = a + b := hl1split
      have : l1Norm (fun j => θhat j - θstar j) = a + b := h2
      rw [this]
      nlinarith [hS1, hcone_ab]

end LassoProof

open HighDimStat.SparseLinear in
theorem solution {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam_pos : 0 < lam)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat) :
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) :=
  LassoProof.main_bound X w θstar θhat S κ lam hSupport hκ hRE hlam_pos hlam hsol
