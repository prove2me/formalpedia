-- Prove2me | solution 1 for LassoDantzig.Equivalence.eq_B17_lasso_side
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:43:03.546182+00:00
-- url     : https://prove2.me/submissions/3f58a9cc-1248-4484-8bb2-8857ce51a549

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

lemma aux_B17_lim {A B C : ℝ} (hB : 0 ≤ B) (h : ∀ t : ℝ, 0 < t → A ≤ t * B + C) : A ≤ C := by
  by_contra hc
  push Not at hc
  have ht : 0 < (A - C) / (B + 1) := div_pos (by linarith) (by linarith)
  have h1 := h _ ht
  have h2 : (A - C) / (B + 1) * B < A - C := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

lemma aux_B17_dir {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (βL : Fin M → ℝ) (hL : IsLasso X y r βL) (v : Fin M → ℝ) :
    (1 / (n:ℝ)) * ∑ i, (y i - X.mulVec βL i) * X.mulVec v i ≤
      r * ∑ j, colNorm X j * |v j| := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 1 / (n:ℝ) := ⟨_, rfl⟩
  have hN : 0 ≤ N := by rw [hNdef]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ i, (y i - X.mulVec βL i) * X.mulVec v i := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ i, X.mulVec v i ^ 2 := ⟨_, rfl⟩
  obtain ⟨pv, hpv⟩ : ∃ pv : ℝ, pv = ∑ j, colNorm X j * |v j| := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, (y i - X.mulVec βL i) ^ 2 := ⟨_, rfl⟩
  obtain ⟨pL, hpL⟩ : ∃ pL : ℝ, pL = ∑ j, colNorm X j * |βL j| := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have key : ∀ t : ℝ, 0 < t → 2 * (N * P) ≤ t * (N * Q) + 2 * (r * pv) := by
    intro t ht
    have h1 := hL (βL + t • v)
    unfold lassoObj at h1
    have hmv : ∀ i, X.mulVec (βL + t • v) i = X.mulVec βL i + t * X.mulVec v i := by
      intro i; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    have hpen : ∑ j, colNorm X j * |(βL + t • v) j| ≤ pL + t * pv := by
      rw [hpL, hpv, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hc : 0 ≤ colNorm X j := Real.sqrt_nonneg _
      have h3 := abs_add_le (βL j) (t * v j)
      rw [abs_mul, abs_of_pos ht] at h3
      nlinarith
    simp only [hmv] at h1
    have hexp : ∑ i, (y i - (X.mulVec βL i + t * X.mulVec v i)) ^ 2
        = S - 2 * t * P + t ^ 2 * Q := by
      rw [hS, hP, hQ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hexp, ← hS, ← hpL, ← hNdef] at h1
    have h4 : 0 ≤ t * (t * (N * Q) + 2 * (r * pv) - 2 * (N * P)) := by
      nlinarith [mul_le_mul_of_nonneg_left hpen (by linarith : (0:ℝ) ≤ 2 * r)]
    have h5 := (mul_nonneg_iff_of_pos_left ht).mp h4
    linarith
  have := aux_B17_lim (mul_nonneg hN hQ0) key
  rw [← hNdef, ← hP, ← hpv]
  linarith

lemma aux_B17_final (F r κ k L1 L2 e W A B : ℝ) (hF : 0 ≤ F) (hr : 0 < r) (hκ : 0 < κ)
    (hk : 0 ≤ k) (hL1 : 0 ≤ L1) (he : 0 ≤ e) (hW : W ≤ F * (2 * L1))
    (hCS : L1 ^ 2 ≤ k * L2 ^ 2) (hke : κ ^ 2 * L2 ^ 2 ≤ e) (hA : A ≤ r * W)
    (hB : B ≤ r / 2 * W) :
    2 * A + 2 * B - e ≤ 9 * F ^ 2 * r ^ 2 * k / κ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 9 * F ^ 2 * r ^ 2 * k / κ ^ 2 := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTk : T * κ ^ 2 = 9 * F ^ 2 * r ^ 2 * k := by
    rw [hT]; field_simp
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 6 * r * F * L1 := ⟨_, rfl⟩
  have hWu : 3 * r * W ≤ u := by
    rw [hu]; have := mul_le_mul_of_nonneg_left hW (by linarith : (0:ℝ) ≤ 3 * r); linarith
  have hu2 : κ ^ 2 * u ^ 2 ≤ κ ^ 2 * (4 * T * e) := by
    have h1 : u ^ 2 = 36 * r ^ 2 * F ^ 2 * L1 ^ 2 := by rw [hu]; ring
    have h2 : 36 * r ^ 2 * F ^ 2 * L1 ^ 2 ≤ 36 * r ^ 2 * F ^ 2 * (k * L2 ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    have h3 : 36 * r ^ 2 * F ^ 2 * k * (κ ^ 2 * L2 ^ 2) ≤ 36 * r ^ 2 * F ^ 2 * k * e :=
      mul_le_mul_of_nonneg_left hke (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ κ ^ 2)
    have h4 : κ ^ 2 * (4 * T * e) = 4 * (T * κ ^ 2) * e := by ring
    rw [h4, hTk, h1]
    linear_combination h5 + h3
  have hu3 : u ^ 2 ≤ (T + e) ^ 2 := by
    have := le_of_mul_le_mul_left hu2 (by positivity : (0:ℝ) < κ ^ 2)
    nlinarith [sq_nonneg (T - e)]
  have hu4 : u ≤ T + e := le_of_pow_le_pow_left₀ (by norm_num) (by linarith) hu3
  nlinarith

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (r : ℝ) (hr : 0 < r) (hw : NoiseEventHalf X r w)
    (βL βD : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL)
    (hD : IsDantzig X (fun i => f i + w i) r βD) (hsp : sparsity βL ≤ s) :
    predLoss X f βL ≤
      predLoss X f βD + 9 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hT0 : 0 ≤ 9 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by positivity
  by_cases hδ0 : βL - βD = 0
  · have : βL = βD := sub_eq_zero.mp hδ0
    have h' : predLoss X f βL = predLoss X f βD := by rw [this]
    linarith
  -- column norm bound
  have hcol : ∀ j, colNorm X j ≤ fmax X := fun j => le_ciSup (Set.finite_range _).bddAbove j
  have hfmax0 : 0 ≤ fmax X := le_trans (Real.sqrt_nonneg _) (hcol ⟨0, by omega⟩)
  -- Dantzig feasibility of the Lasso
  have hfeas : DantzigFeasible X (fun i => f i + w i) r βL := by
    intro j
    have h1 := aux_B17_dir X _ r hr.le βL hL (Pi.single j 1)
    have h2 := aux_B17_dir X _ r hr.le βL hL (-(Pi.single j 1))
    have e1 : ∀ i, X.mulVec (Pi.single j 1) i = X i j := by
      intro i; simp
    have e2 : ∑ j', colNorm X j' * |(Pi.single j (1:ℝ) : Fin M → ℝ) j'| = colNorm X j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have e3 : ∑ j', colNorm X j' * |(-(Pi.single j (1:ℝ)) : Fin M → ℝ) j'| = colNorm X j := by
      simp only [Pi.neg_apply, abs_neg]; exact e2
    rw [e2] at h1
    rw [e3, Matrix.mulVec_neg] at h2
    simp only [e1, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1 h2
    rw [abs_le]
    have e4 : ∑ i, X i j * (f i + w i - X.mulVec βL i)
        = ∑ i, (f i + w i - X.mulVec βL i) * X i j := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e4]
    constructor <;> nlinarith
  set δ := βL - βD with hδ
  set J := supp βL with hJ
  have hJc : ∀ j ∈ Jᶜ, βL j = 0 := by intro j hj; simpa [J, supp] using hj
  have hcone : l1On δ Jᶜ ≤ l1On δ J := by
    have e1 := Finset.sum_add_sum_compl J (fun j => |βD j|)
    have e2 := Finset.sum_add_sum_compl J (fun j => |βL j|)
    have z1 : ∑ j ∈ Jᶜ, |βL j| = 0 := Finset.sum_eq_zero (fun j hj => by simp [hJc j hj])
    have z2 : ∑ j ∈ Jᶜ, |βD j| = l1On δ Jᶜ := by
      unfold l1On; apply Finset.sum_congr rfl; intro j hj; simp [δ, hJc j hj]
    have z3 : ∑ j ∈ J, |βL j| - l1On δ J ≤ ∑ j ∈ J, |βD j| := by
      unfold l1On; rw [← Finset.sum_sub_distrib]; apply Finset.sum_le_sum; intro j _
      simp only [δ, Pi.sub_apply]
      have := abs_add_le (βL j - βD j) (βD j); rw [sub_add_cancel] at this; linarith
    have := hD.2 βL hfeas
    linarith
  have hl1split : ∑ j, |δ j| = l1On δ J + l1On δ Jᶜ := by
    unfold l1On; rw [Finset.sum_add_sum_compl]
  have hw1 : ∑ j, colNorm X j * |δ j| ≤ fmax X * (2 * l1On δ J) := by
    calc ∑ j, colNorm X j * |δ j| ≤ ∑ j, fmax X * |δ j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg _))
      _ = fmax X * ∑ j, |δ j| := by rw [Finset.mul_sum]
      _ ≤ fmax X * (2 * l1On δ J) := by apply mul_le_mul_of_nonneg_left _ hfmax0; linarith
  have hCS : l1On δ J ^ 2 ≤ (sparsity βL : ℝ) * l2On δ J ^ 2 := by
    unfold l1On l2On
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    have := sq_sum_le_card_mul_sum_sq (s := J) (f := fun j => |δ j|)
    simpa [sq_abs, sparsity, J] using this
  have hREδ := hRE J hsp δ hδ0 (by unfold ConeCond; linarith)
  have hd : ∀ i, X.mulVec δ i = X.mulVec βL i - X.mulVec βD i := by
    intro i; simp [δ, Matrix.mulVec_sub]
  have hdn : ∀ i, X.mulVec (-δ) i = -(X.mulVec βL i - X.mulVec βD i) := by
    intro i; simp [Matrix.mulVec_neg, hd]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ i, (X.mulVec βL i - X.mulVec βD i) ^ 2 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hl20 : 0 ≤ l2On δ J := Real.sqrt_nonneg _
  have hRE2 : κ ^ 2 * (n:ℝ) * l2On δ J ^ 2 ≤ E := by
    have h0 : 0 ≤ κ * Real.sqrt n * l2On δ J := by positivity
    have := pow_le_pow_left₀ h0 hREδ 2
    unfold euclNorm at this
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), mul_pow, mul_pow,
      Real.sq_sqrt hnR.le] at this
    simp only [hd] at this
    rw [hE]; exact this
  have hnoise : (1 / (n:ℝ)) * ∑ i, X.mulVec δ i * w i ≤ r / 2 * ∑ j, colNorm X j * |δ j| := by
    have eq : (1 / (n:ℝ)) * ∑ i, X.mulVec δ i * w i
        = ∑ j, δ j * ((1 / (n:ℝ)) * ∑ i, X i j * w i) := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [eq, Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    have := hw j
    have h1 : δ j * ((1 / (n:ℝ)) * ∑ i, X i j * w i)
        ≤ |δ j| * |(1 / (n:ℝ)) * ∑ i, X i j * w i| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |δ j| * |(1 / (n:ℝ)) * ∑ i, X i j * w i| ≤ |δ j| * (r * colNorm X j / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    nlinarith
  have hdir := aux_B17_dir X _ r hr.le βL hL (-δ)
  simp only [hdn, Pi.neg_apply, abs_neg] at hdir
  simp only [hd] at hnoise
  have hdiff : predLoss X f βL - predLoss X f βD
      = 2 * ((1 / (n:ℝ)) * ∑ i, (f i + w i - X.mulVec βL i) *
          -(X.mulVec βL i - X.mulVec βD i))
        + 2 * ((1 / (n:ℝ)) * ∑ i, (X.mulVec βL i - X.mulVec βD i) * w i)
        - (1 / (n:ℝ)) * E := by
    unfold predLoss
    rw [hE]
    have : ∑ i, (X.mulVec βL i - f i) ^ 2 - ∑ i, (X.mulVec βD i - f i) ^ 2
        = 2 * ∑ i, (f i + w i - X.mulVec βL i) *
          -(X.mulVec βL i - X.mulVec βD i)
          + 2 * ∑ i, (X.mulVec βL i - X.mulVec βD i) * w i
          - ∑ i, (X.mulVec βL i - X.mulVec βD i) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    linear_combination (1 / (n:ℝ)) * this
  have hke : κ ^ 2 * l2On δ J ^ 2 ≤ (1 / (n:ℝ)) * E := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hnR]; linarith
  have hL10 : 0 ≤ l1On δ J := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hfin := aux_B17_final (fmax X) r κ (sparsity βL : ℝ) (l1On δ J) (l2On δ J)
    ((1 / (n:ℝ)) * E) (∑ j, colNorm X j * |δ j|) _ _ hfmax0 hr hκ (by positivity) hL10
    (by positivity) hw1 hCS hke hdir hnoise
  rw [← hdiff] at hfin
  linarith only [hfin]
