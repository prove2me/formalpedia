-- Prove2me | solution 1 for LassoDantzig.Oracle.before_decoupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:46:27.604986+00:00
-- url     : https://prove2.me/submissions/bc7e10e3-4324-42b4-b6cf-55429746d3fd

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace BD8e530a9c
open LassoDantzig.Oracle

lemma empSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ empSq v := by
  unfold empSq; positivity

lemma colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j :=
  Real.sqrt_nonneg _

lemma le_fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : colNorm X j ≤ fmax X :=
  le_ciSup (Set.finite_range _).bddAbove j

lemma fmin_le {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : fmin X ≤ colNorm X j :=
  ciInf_le (Set.finite_range _).bddBelow j

lemma fmin_pos {n M : ℕ} (hM : 1 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) : 0 < fmin X := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨j, hj⟩ : ∃ j, colNorm X j = fmin X := exists_eq_ciInf_of_finite
  rw [← hj]
  exact lt_of_le_of_ne (colNorm_nonneg X j) (Ne.symm (hcol j))

lemma fmax_nonneg {n M : ℕ} (hM : 1 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ) : 0 ≤ fmax X :=
  le_trans (colNorm_nonneg X ⟨0, hM⟩) (le_fmax X _)

lemma mv {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) (i : Fin n) :
    X.mulVec x i = ∑ j, X i j * x j := rfl

lemma cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ) (δ : Fin M → ℝ) :
    ∑ i, w i * X.mulVec δ i = ∑ j, δ j * ∑ i, X i j * w i := by
  simp_rw [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

lemma l1_le_sqrt_card {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1On δ J ≤ √(J.card : ℝ) * l2On δ J := by
  unfold l1On l2On
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  have := sq_sum_le_card_mul_sum_sq (s := J) (f := fun j => |δ j|)
  simpa [sq_abs] using this

lemma mink {n : ℕ} (p q : Fin n → ℝ) :
    √(∑ i, (p i - q i) ^ 2) ≤ √(∑ i, p i ^ 2) + √(∑ i, q i ^ 2) := by
  have hP : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ p (fun i => - q i)
  simp only [neg_sq] at cs
  have e : ∑ i, (p i - q i) ^ 2 = ∑ i, p i ^ 2 + ∑ i, q i ^ 2 + 2 * ∑ i, p i * (- q i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : ∑ i, (p i - q i) ^ 2 ≤ (√(∑ i, p i ^ 2) + √(∑ i, q i ^ 2)) ^ 2 := by
    rw [e, add_sq, Real.sq_sqrt hP, Real.sq_sqrt hQ]
    nlinarith [cs]
  calc √(∑ i, (p i - q i) ^ 2) ≤ √((√(∑ i, p i ^ 2) + √(∑ i, q i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = √(∑ i, p i ^ 2) + √(∑ i, q i ^ 2) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

lemma empNorm_sub_le {n : ℕ} (p q : Fin n → ℝ) :
    empNorm (fun i => p i - q i) ≤ empNorm p + empNorm q := by
  unfold empNorm empSq
  have hn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  rw [Real.sqrt_mul hn, Real.sqrt_mul hn, Real.sqrt_mul hn, ← mul_add]
  exact mul_le_mul_of_nonneg_left (mink p q) (Real.sqrt_nonneg _)

lemma basic {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (βhat β : Fin M → ℝ) (hL : IsLasso X y r βhat) :
    empSq (fun i => X.mulVec βhat i - f i) +
        r * (∑ j ∈ supp β, colNorm X j * |βhat j - β j| +
          ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j|)
      ≤ empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
  have h := hL β
  simp only [lassoObj, empSq] at h
  simp only [empSq]
  set J := supp β with hJ
  set A := ∑ j ∈ J, colNorm X j * |βhat j - β j| with hAdef
  set B := ∑ j ∈ Jᶜ, colNorm X j * |βhat j - β j| with hBdef
  have hmv : ∀ i, X.mulVec βhat i = X.mulVec β i + X.mulVec (βhat - β) i := by
    intro i; rw [Matrix.mulVec_sub, Pi.sub_apply]; ring
  have hpt : ∀ i, (X.mulVec βhat i - f i) ^ 2 = (X.mulVec β i - f i) ^ 2 +
      (y i - X.mulVec βhat i) ^ 2 - (y i - X.mulVec β i) ^ 2 +
      2 * ((y i - f i) * X.mulVec (βhat - β) i) := by
    intro i; rw [hmv i]; ring
  have hsum : ∑ i, (X.mulVec βhat i - f i) ^ 2 = ∑ i, (X.mulVec β i - f i) ^ 2 +
      ∑ i, (y i - X.mulVec βhat i) ^ 2 - ∑ i, (y i - X.mulVec β i) ^ 2 +
      2 * ∑ i, (y i - f i) * X.mulVec (βhat - β) i := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- cross term bound
  have hC : (1 / (n : ℝ)) * (2 * ∑ i, (y i - f i) * X.mulVec (βhat - β) i) ≤ r * (A + B) := by
    have e : (1 / (n : ℝ)) * (2 * ∑ i, (y i - f i) * X.mulVec (βhat - β) i) =
        ∑ j, (βhat j - β j) * (2 * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - f i))) := by
      rw [cross]
      simp only [Finset.mul_sum, Pi.sub_apply]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e, hAdef, hBdef, Finset.sum_add_sum_compl, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj := hA j
    calc (βhat j - β j) * (2 * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)))
        ≤ |(βhat j - β j) * (2 * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)))| := le_abs_self _
      _ = |βhat j - β j| * (2 * |(1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)|) := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ |βhat j - β j| * (r * colNorm X j) := mul_le_mul_of_nonneg_left hj (abs_nonneg _)
      _ = r * (colNorm X j * |βhat j - β j|) := by ring
  -- penalty difference
  have hP : ∑ j, colNorm X j * |β j| - ∑ j, colNorm X j * |βhat j| ≤ A - B := by
    rw [← Finset.sum_add_sum_compl J (fun j => colNorm X j * |β j|),
      ← Finset.sum_add_sum_compl J (fun j => colNorm X j * |βhat j|)]
    have h1 : ∑ j ∈ J, colNorm X j * |β j| - ∑ j ∈ J, colNorm X j * |βhat j| ≤ A := by
      rw [hAdef, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      have := abs_sub_abs_le_abs_sub (β j) (βhat j)
      rw [abs_sub_comm] at this
      have hc := colNorm_nonneg X j
      nlinarith
    have h2 : ∑ j ∈ Jᶜ, colNorm X j * |β j| - ∑ j ∈ Jᶜ, colNorm X j * |βhat j| = -B := by
      rw [hBdef, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have : β j = 0 := by
        rw [Finset.mem_compl, hJ, supp, Finset.mem_filter] at hj
        simpa using hj
      simp [this]
    linarith
  have hd : (1 / (n : ℝ)) * ∑ i, (X.mulVec βhat i - f i) ^ 2 =
      (1 / (n : ℝ)) * ∑ i, (X.mulVec β i - f i) ^ 2 +
      (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec βhat i) ^ 2 -
      (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 +
      (1 / (n : ℝ)) * (2 * ∑ i, (y i - f i) * X.mulVec (βhat - β) i) := by
    rw [hsum]; ring
  have hP2 := mul_le_mul_of_nonneg_left hP (show (0 : ℝ) ≤ 2 * r by positivity)
  have e3 : 2 * r * (∑ j, colNorm X j * |β j| - ∑ j, colNorm X j * |βhat j|) =
      2 * r * ∑ j, colNorm X j * |β j| - 2 * r * ∑ j, colNorm X j * |βhat j| := by ring
  linarith [hd, hC, hP2, h, e3]

end BD8e530a9c

open LassoDantzig.Oracle in
theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ)
    (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) (hβs : sparsity β ≤ s)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    empSq (fun i => X.mulVec βhat i - f i) ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            empNorm (fun i => X.mulVec βhat i - X.mulVec β i) ∧
      empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            empNorm (fun i => X.mulVec βhat i - X.mulVec β i) ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            (empNorm (fun i => X.mulVec βhat i - f i) + empNorm (fun i => X.mulVec β i - f i)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM1 : 1 ≤ M := by omega
  have hbasic := BD8e530a9c.basic X f y r hr hA βhat β hL
  have hfmin := BD8e530a9c.fmin_pos hM1 X hcol
  have hfmax0 := BD8e530a9c.fmax_nonneg hM1 X
  have hu := BD8e530a9c.empSq_nonneg (fun i => X.mulVec β i - f i)
  have hv := BD8e530a9c.empSq_nonneg (fun i => X.mulVec βhat i - f i)
  set u := empSq (fun i => X.mulVec β i - f i) with hudef
  set v := empSq (fun i => X.mulVec βhat i - f i) with hvdef
  set J := supp β with hJ
  set A := ∑ j ∈ J, colNorm X j * |βhat j - β j| with hAdef
  set B := ∑ j ∈ Jᶜ, colNorm X j * |βhat j - β j| with hBdef
  set δ : Fin M → ℝ := βhat - β with hδ
  have hA0 : 0 ≤ A := Finset.sum_nonneg
    (fun j _ => mul_nonneg (BD8e530a9c.colNorm_nonneg X j) (abs_nonneg _))
  have hB0 : 0 ≤ B := Finset.sum_nonneg
    (fun j _ => mul_nonneg (BD8e530a9c.colNorm_nonneg X j) (abs_nonneg _))
  have hrA : r * (A + B) = r * A + r * B := mul_add r A B
  -- B ≤ (3 + 4/ε) A
  have hBle : B ≤ (3 + 4 / ε) * A := by
    have h1 : r * B ≤ u + 3 * r * A := by linarith
    have h3 : ε * (r * B) ≤ ε * u + ε * (3 * r * A) := by nlinarith
    have h4 : r * (ε * B) ≤ r * ((4 + 3 * ε) * A) := by nlinarith
    have h5 : ε * B ≤ (4 + 3 * ε) * A := le_of_mul_le_mul_left h4 hr
    have e : (3 + 4 / ε) * A = ((4 + 3 * ε) * A) / ε := by
      field_simp
      ring
    rw [e, le_div_iff₀ hε]
    linarith
  -- weighted l1 bounds
  have hAle : A ≤ fmax X * l1On δ J := by
    rw [l1On, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := BD8e530a9c.le_fmax X j
    have e : δ j = βhat j - β j := rfl
    rw [e]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hBge : fmin X * l1On δ Jᶜ ≤ B := by
    rw [l1On, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := BD8e530a9c.fmin_le X j
    have e : δ j = βhat j - β j := rfl
    rw [e]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hl1J : 0 ≤ l1On δ J := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcone : ConeCond ((3 + 4 / ε) * fmax X / fmin X) J δ := by
    unfold ConeCond
    rw [show (3 + 4 / ε) * fmax X / fmin X * l1On δ J =
        ((3 + 4 / ε) * fmax X * l1On δ J) / fmin X by ring, le_div_iff₀ hfmin]
    have hc : 0 ≤ 3 + 4 / ε := by positivity
    have := mul_le_mul_of_nonneg_left hAle hc
    nlinarith
  have hδne : δ ≠ 0 := by
    intro h0
    have hz : ∀ j, βhat j - β j = 0 := fun j => by
      have := congrFun h0 j
      simpa [hδ] using this
    have hA00 : A = 0 := by simp [hAdef, hz]
    have h4 : 4 * r * A = 0 := by rw [hA00]; ring
    have := mul_nonneg hε.le hu
    linarith
  have hRE' := hRE J hβs δ hδne hcone
  set E := empNorm (fun i => X.mulVec βhat i - X.mulVec β i) with hEdef
  have hg : (fun i => X.mulVec βhat i - X.mulVec β i) = X.mulVec δ := by
    funext i; rw [hδ, Matrix.mulVec_sub, Pi.sub_apply]
  have hE : euclNorm (X.mulVec δ) = √(n : ℝ) * E := by
    rw [hEdef, hg]
    unfold euclNorm empNorm empSq
    rw [← Real.sqrt_mul hn'.le]
    congr 1
    field_simp
  rw [hE] at hRE'
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have hκL2 : κ * l2On δ J ≤ E := by
    have : √(n : ℝ) * (κ * l2On δ J) ≤ √(n : ℝ) * E := by linarith
    exact le_of_mul_le_mul_left this hsn
  have hl12 := BD8e530a9c.l1_le_sqrt_card δ J
  have hcard : ((J.card : ℕ) : ℝ) = (sparsity β : ℝ) := rfl
  rw [hcard] at hl12
  have hsq0 : 0 ≤ √(sparsity β : ℝ) := Real.sqrt_nonneg _
  have s1 := mul_le_mul_of_nonneg_left hAle hκ.le
  have s2 : fmax X * l1On δ J ≤ fmax X * (√(sparsity β : ℝ) * l2On δ J) :=
    mul_le_mul_of_nonneg_left hl12 hfmax0
  have s2' := mul_le_mul_of_nonneg_left s2 hκ.le
  have s3 : fmax X * √(sparsity β : ℝ) * (κ * l2On δ J) ≤ fmax X * √(sparsity β : ℝ) * E :=
    mul_le_mul_of_nonneg_left hκL2 (mul_nonneg hfmax0 hsq0)
  have hκA : κ * A ≤ fmax X * √(sparsity β : ℝ) * E := by nlinarith
  have hAfin : A ≤ fmax X * κ⁻¹ * √(sparsity β : ℝ) * E := by
    have := mul_le_mul_of_nonneg_left hκA (inv_nonneg.mpr hκ.le)
    rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul] at this
    calc A ≤ κ⁻¹ * (fmax X * √(sparsity β : ℝ) * E) := this
      _ = fmax X * κ⁻¹ * √(sparsity β : ℝ) * E := by ring
  have hcoef : 0 ≤ 4 * r * fmax X * κ⁻¹ * √(sparsity β : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hfmax0) (inv_nonneg.mpr hκ.le)) hsq0
  refine ⟨?_, ?_⟩
  · have h4 := mul_le_mul_of_nonneg_left hAfin (show (0 : ℝ) ≤ 4 * r by positivity)
    have : 4 * r * (fmax X * κ⁻¹ * √(sparsity β : ℝ) * E) =
        4 * r * fmax X * κ⁻¹ * √(sparsity β : ℝ) * E := by ring
    nlinarith
  · have tri := BD8e530a9c.empNorm_sub_le (fun i => X.mulVec βhat i - f i)
      (fun i => X.mulVec β i - f i)
    have e2 : (fun i => (X.mulVec βhat i - f i) - (X.mulVec β i - f i)) =
        (fun i => X.mulVec βhat i - X.mulVec β i) := by funext i; ring
    simp only [e2] at tri
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left tri hcoef)
