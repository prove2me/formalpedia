-- Prove2me | solution 1 for LassoDantzig.Equivalence.eq_B15_dantzig_side
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:41:50.511973+00:00
-- url     : https://prove2.me/submissions/fdc53b36-3359-45e1-9e45-964fe821e5c6

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

lemma aux_eqB15_colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j := Real.sqrt_nonneg _

lemma aux_eqB15_colNorm_le_fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    colNorm X j ≤ fmax X :=
  le_ciSup (Set.finite_range _).bddAbove j

lemma aux_eqB15_abs_le {g c a : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 2 * t * g ≤ t ^ 2 * c + 2 * a * |t|) : |g| ≤ a := by
  have key : ∀ g' : ℝ, (∀ t : ℝ, 0 < t → 2 * t * g' ≤ t ^ 2 * c + 2 * a * t) → g' ≤ a := by
    intro g' hg'
    by_contra hlt
    rw [not_le] at hlt
    set t := (g' - a) / (c + 1) with ht
    have htpos : 0 < t := div_pos (by linarith) (by linarith)
    have h1 := hg' t htpos
    have h2 : 2 * g' ≤ t * c + 2 * a := by
      have : t * (2 * g') ≤ t * (t * c + 2 * a) := by nlinarith
      exact le_of_mul_le_mul_left this htpos
    have h3 : t * c < g' - a := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  rw [abs_le]
  constructor
  · have := key (-g) (fun t ht => by
      have := h (-t)
      rw [abs_neg, abs_of_pos ht, neg_sq] at this
      linarith)
    linarith
  · exact key g (fun t ht => by
      have := h t
      rw [abs_of_pos ht] at this
      linarith)

lemma aux_eqB15_lasso_feas {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (βL : Fin M → ℝ) (hL : IsLasso X y r βL) : DantzigFeasible X y r βL := by
  intro j
  set g := (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βL i) with hg
  set c := (1 / (n : ℝ)) * ∑ i, X i j ^ 2 with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  apply aux_eqB15_abs_le hc0
  intro t
  have h := hL (fun k => βL k + if k = j then t else 0)
  unfold lassoObj at h
  have hmv : ∀ i, X.mulVec (fun k => βL k + if k = j then t else 0) i
      = X.mulVec βL i + t * X i j := by
    intro i
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_comm]
  have hpen : ∑ k, colNorm X k * |βL k + if k = j then t else 0|
      ≤ ∑ k, colNorm X k * |βL k| + colNorm X j * |t| := by
    have hk : ∀ k, colNorm X k * |βL k + if k = j then t else 0|
        ≤ colNorm X k * |βL k| + colNorm X k * |if k = j then t else 0| := by
      intro k
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (aux_eqB15_colNorm_nonneg X k)
    calc _ ≤ ∑ k, (colNorm X k * |βL k| + colNorm X k * |if k = j then t else 0|) :=
          Finset.sum_le_sum (fun k _ => hk k)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [apply_ite]
  have hquad : (1 / (n:ℝ)) * ∑ i, (y i - X.mulVec (fun k => βL k + if k = j then t else 0) i) ^ 2
      = (1 / (n:ℝ)) * ∑ i, (y i - X.mulVec βL i) ^ 2 - 2 * t * g + t ^ 2 * c := by
    simp only [hmv, hg, hc]
    have e : ∀ i, (y i - (X.mulVec βL i + t * X i j)) ^ 2
        = (y i - X.mulVec βL i) ^ 2 - 2 * t * (X i j * (y i - X.mulVec βL i))
          + t ^ 2 * X i j ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hquad] at h
  nlinarith [mul_le_mul_of_nonneg_left hpen (by linarith : (0:ℝ) ≤ 2 * r)]

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (r : ℝ) (hr : 0 < r) (hw : NoiseEvent X r w)
    (βL βD : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL)
    (hD : IsDantzig X (fun i => f i + w i) r βD) (hsp : sparsity βL ≤ s) :
    predLoss X f βD ≤
      predLoss X f βL + 16 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by
  set y : Fin n → ℝ := fun i => f i + w i with hy
  set J0 := supp βL with hJ0
  set δ : Fin M → ℝ := βD - βL with hδ
  set F := fmax X with hF
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hF0 : 0 ≤ F := by
    have j0 : Fin M := ⟨0, by omega⟩
    exact le_trans (aux_eqB15_colNorm_nonneg X j0) (aux_eqB15_colNorm_le_fmax X j0)
  -- the Lasso is Dantzig feasible, hence `|βD|₁ ≤ |βL|₁`
  have hLfeas := aux_eqB15_lasso_feas X y r hr.le βL hL
  have hl1 : ∑ j, |βD j| ≤ ∑ j, |βL j| := hD.2 βL hLfeas
  -- cone condition
  have hoff : ∀ j ∈ J0ᶜ, βL j = 0 := by
    intro j hj
    simpa [hJ0, supp] using hj
  have hcone : ConeCond 1 J0 δ := by
    unfold ConeCond l1On
    have e1 := Finset.sum_add_sum_compl J0 (fun j => |βD j|)
    have e2 := Finset.sum_add_sum_compl J0 (fun j => |βL j|)
    have z2 : ∑ j ∈ J0ᶜ, |βL j| = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hoff j hj, abs_zero])
    have z1 : ∑ j ∈ J0ᶜ, |βD j| = ∑ j ∈ J0ᶜ, |δ j| :=
      Finset.sum_congr rfl (fun j hj => by simp [hδ, hoff j hj])
    have t1 : ∑ j ∈ J0, |βL j| ≤ ∑ j ∈ J0, |βD j| + ∑ j ∈ J0, |δ j| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have : βL j = βD j + (-δ j) := by simp [hδ]
      rw [this, ← abs_neg (δ j)]
      exact abs_add_le _ _
    linarith
  -- Cauchy-Schwarz on J0
  set L := l2On δ J0 with hLdef
  set m : ℕ := sparsity βL with hm
  have hmJ : J0.card = m := rfl
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hCS : l1On δ J0 ≤ Real.sqrt m * L := by
    unfold l1On
    rw [hLdef, l2On, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    have hs0 : 0 ≤ ∑ j ∈ J0, |δ j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    rw [← Real.sqrt_sq hs0]
    apply Real.sqrt_le_sqrt
    have := sq_sum_le_card_mul_sum_sq (s := J0) (f := fun j => |δ j|)
    simpa [sq_abs, hmJ] using this
  -- total ℓ1 norm
  have htot : ∑ j, |δ j| ≤ 2 * (Real.sqrt m * L) := by
    have e := Finset.sum_add_sum_compl J0 (fun j => |δ j|)
    have hc := hcone
    unfold ConeCond l1On at hc
    unfold l1On at hCS
    linarith
  -- restricted eigenvalue
  set v : Fin n → ℝ := X.mulVec δ with hv
  set Q : ℝ := ∑ i, v i ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRE' : κ * Real.sqrt n * L ≤ Real.sqrt Q := by
    by_cases hδ0 : δ = 0
    · have : L = 0 := by simp [hLdef, l2On, hδ0]
      rw [this, mul_zero]
      exact Real.sqrt_nonneg _
    · exact hRE J0 hsp δ hδ0 hcone
  -- expansion of the difference of losses
  have hvi : ∀ i, v i = X.mulVec βD i - X.mulVec βL i := by
    intro i
    simp [hv, hδ, Matrix.mulVec_sub]
  set a : Fin n → ℝ := fun i => X.mulVec βD i - f i with ha
  have hdiff : predLoss X f βD - predLoss X f βL
      = 2 * ((1 / (n:ℝ)) * ∑ i, v i * a i) - (1 / (n:ℝ)) * Q := by
    unfold predLoss
    have e : ∀ i, (X.mulVec βD i - f i) ^ 2 - (X.mulVec βL i - f i) ^ 2
        = 2 * (v i * a i) - v i ^ 2 := by
      intro i
      rw [hvi i, ha]
      ring
    have : ∑ i, (X.mulVec βD i - f i) ^ 2 - ∑ i, (X.mulVec βL i - f i) ^ 2
        = 2 * ∑ i, v i * a i - Q := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => e i),
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← mul_sub, this]
    ring
  -- swap sums
  set G : Fin M → ℝ := fun j => (1 / (n:ℝ)) * ∑ i, X i j * a i with hG
  have hswap : (1 / (n:ℝ)) * ∑ i, v i * a i = ∑ j, δ j * G j := by
    have : ∑ i, v i * a i = ∑ j, δ j * ∑ i, X i j * a i := by
      simp only [hv, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      ring
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hG]
    ring
  have hGb : ∀ j, |G j| ≤ 2 * r * F := by
    intro j
    have hsplit : G j = (1 / (n:ℝ)) * ∑ i, X i j * w i
        - (1 / (n:ℝ)) * ∑ i, X i j * (y i - X.mulVec βD i) := by
      simp only [hG, ha, hy, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have h1 := hw j
    have h2 := hD.1 j
    have h3 := aux_eqB15_colNorm_le_fmax X j
    rw [hsplit]
    calc _ ≤ |(1 / (n:ℝ)) * ∑ i, X i j * w i|
          + |(1 / (n:ℝ)) * ∑ i, X i j * (y i - X.mulVec βD i)| := abs_sub _ _
      _ ≤ r * colNorm X j + r * colNorm X j := add_le_add h1 h2
      _ ≤ 2 * r * F := by nlinarith
  have hcross : ∑ j, δ j * G j ≤ 2 * r * F * ∑ j, |δ j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    calc δ j * G j ≤ |δ j * G j| := le_abs_self _
      _ = |δ j| * |G j| := abs_mul _ _
      _ ≤ |δ j| * (2 * r * F) := mul_le_mul_of_nonneg_left (hGb j) (abs_nonneg _)
      _ = 2 * r * F * |δ j| := by ring
  -- final quadratic estimate
  set u : ℝ := Real.sqrt Q / Real.sqrt n with hu
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hu2 : u ^ 2 = (1 / (n:ℝ)) * Q := by
    rw [hu, div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hn'.le]
    ring
  have hκL : κ * L ≤ u := by
    rw [hu, le_div_iff₀ hsn]
    nlinarith
  set b : ℝ := r * F * Real.sqrt m / κ with hb
  have hb0 : 0 ≤ b := div_nonneg (mul_nonneg (mul_nonneg hr.le hF0) (Real.sqrt_nonneg _)) hκ.le
  have hbκ : b * κ = r * F * Real.sqrt m := by
    rw [hb]; field_simp
  have hb2 : 16 * b ^ 2 = 16 * F ^ 2 * r ^ 2 * (m : ℝ) / κ ^ 2 := by
    rw [hb, div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hmain : 2 * (∑ j, δ j * G j) ≤ 8 * b * u := by
    have h1 : 2 * (∑ j, δ j * G j) ≤ 8 * (r * F * Real.sqrt m) * L := by
      have := mul_le_mul_of_nonneg_left htot (by positivity : (0:ℝ) ≤ 2 * r * F)
      nlinarith
    rw [← hbκ] at h1
    have h2 : b * (κ * L) ≤ b * u := mul_le_mul_of_nonneg_left hκL hb0
    nlinarith
  have hfin : predLoss X f βD - predLoss X f βL ≤ 16 * b ^ 2 := by
    rw [hdiff, hswap, ← hu2]
    nlinarith [sq_nonneg (u - 4 * b)]
  rw [hb2] at hfin
  linarith
