-- Prove2me | solution 1 for LassoDantzig.REConditions.assumption3_implies_RE
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:29:31.968834+00:00
-- url     : https://prove2.me/submissions/03c4180e-c1b3-499c-8e16-d2c0b566338a

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

lemma aux_a3re_mulVec_sq {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (c : Fin M → ℝ) :
    ∑ i, (X.mulVec c i) ^ 2 ≤ (∑ i, ∑ j, X i j ^ 2) * ∑ j, c j ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma aux_a3re_sum_sq_pos {M : ℕ} (c : Fin M → ℝ) (hc : c ≠ 0) : 0 < ∑ j, c j ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  have hj' : 0 < c j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))
  exact lt_of_lt_of_le hj'
    (Finset.single_le_sum (fun k _ => sq_nonneg (c k)) (Finset.mem_univ j))

lemma aux_a3re_corr_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) :
    BddAbove (corrSet X m1 m2) := by
  refine ⟨(∑ i, ∑ j, X i j ^ 2) / n, ?_⟩
  rintro t ⟨I1, I2, _, _, _, c1, c2, _, _, hc1, hc2, rfl⟩
  have hF : 0 ≤ ∑ i, ∑ j, X i j ^ 2 := by positivity
  set F := ∑ i, ∑ j, X i j ^ 2 with hFdef
  have hA := aux_a3re_sum_sq_pos c1 hc1
  have hB := aux_a3re_sum_sq_pos c2 hc2
  set A := ∑ j, c1 j ^ 2 with hAdef
  set B := ∑ j, c2 j ^ 2 with hBdef
  rcases Nat.eq_zero_or_pos n with h0 | hnpos
  · subst h0; simp
  have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
  have hS1 := aux_a3re_mulVec_sq X c1
  have hS2 := aux_a3re_mulVec_sq X c2
  have hS1n : 0 ≤ ∑ i, (X.mulVec c1 i) ^ 2 := by positivity
  have hS2n : 0 ≤ ∑ i, (X.mulVec c2 i) ^ 2 := by positivity
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X.mulVec c1) (X.mulVec c2)
  have hnum : ∑ i, X.mulVec c1 i * X.mulVec c2 i ≤ F * Real.sqrt A * Real.sqrt B := by
    apply le_trans (le_abs_self _)
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    calc (∑ i, X.mulVec c1 i * X.mulVec c2 i) ^ 2
        ≤ (∑ i, (X.mulVec c1 i) ^ 2) * ∑ i, (X.mulVec c2 i) ^ 2 := hCS
      _ ≤ (F * A) * (F * B) := mul_le_mul hS1 hS2 hS2n (by positivity)
      _ = F ^ 2 * A * B := by ring
  have hpos : 0 < (n : ℝ) * Real.sqrt A * Real.sqrt B := by positivity
  rw [div_le_div_iff₀ hpos hn']
  calc (∑ i, X.mulVec c1 i * X.mulVec c2 i) * n ≤ (F * Real.sqrt A * Real.sqrt B) * n :=
        mul_le_mul_of_nonneg_right hnum hn'.le
    _ = F * (n * Real.sqrt A * Real.sqrt B) := by ring

lemma aux_a3re_cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n) (s : ℕ)
    (J0 : Finset (Fin M)) (hJ : J0.card ≤ s) (a : Fin M → ℝ) (ha : ∀ j, j ∉ J0 → a j = 0)
    (ha0 : a ≠ 0) (k : Fin M) (hk : k ∉ J0) :
    |∑ i, X.mulVec a i * X i k| ≤ n * theta X s 1 * Real.sqrt (∑ j, a j ^ 2) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hA := aux_a3re_sum_sq_pos a ha0
  have key : ∀ r : ℝ, r ≠ 0 →
      (∑ i, X.mulVec a i * X.mulVec (Pi.single k r) i) /
        ((n : ℝ) * Real.sqrt (∑ j, a j ^ 2) *
          Real.sqrt (∑ j, (Pi.single k r : Fin M → ℝ) j ^ 2)) ≤ theta X s 1 := by
    intro r hr
    apply le_csSup (aux_a3re_corr_bdd X s 1)
    refine ⟨J0, {k}, Finset.disjoint_singleton_right.mpr hk, hJ, by simp, a, Pi.single k r,
      ha, ?_, ha0, ?_, rfl⟩
    · intro j hj
      rw [Finset.mem_singleton] at hj
      simp [hj]
    · intro h
      have := congrFun h k
      simp at this
      exact hr this
  have hsq : ∀ r : ℝ, ∑ j, (Pi.single k r : Fin M → ℝ) j ^ 2 = r ^ 2 := by
    intro r
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have h1 := key 1 one_ne_zero
  have h2 := key (-1) (by norm_num)
  rw [hsq] at h1 h2
  simp only [Matrix.mulVec_single, Matrix.col] at h1 h2
  have hpos : 0 < (n : ℝ) * Real.sqrt (∑ j, a j ^ 2) := by positivity
  norm_num at h1 h2
  rw [div_le_iff₀ hpos] at h1 h2
  rw [abs_le]
  constructor
  · linarith
  · linarith

lemma aux_a3re_theta_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (hs : 1 ≤ s) : 0 ≤ theta X s 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set i0 : Fin M := ⟨0, by omega⟩
  set i1 : Fin M := ⟨1, by omega⟩
  have hne : i1 ∉ ({i0} : Finset (Fin M)) := by
    simp [i0, i1, Fin.ext_iff]
  have h := aux_a3re_cross X hn s {i0} (by simpa using hs) (Pi.single i0 1)
    (by intro j hj; rw [Finset.mem_singleton] at hj; simp [hj]) (by simp) i1 hne
  have hsum : ∑ j, (Pi.single i0 (1:ℝ) : Fin M → ℝ) j ^ 2 = 1 := by
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [hsum, Real.sqrt_one, mul_one] at h
  have h0 := le_trans (abs_nonneg _) h
  by_contra hneg
  push Not at hneg
  have : (n : ℝ) * theta X s 1 < 0 := mul_neg_of_pos_of_neg hn' hneg
  linarith

lemma aux_a3re_bilin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (v : Fin n → ℝ) (b : Fin M → ℝ) :
    ∑ i, v i * X.mulVec b i = ∑ k, b k * ∑ i, v i * X i k := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => by ring))

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA3 : 2 * c0 * theta X s 1 * Real.sqrt s < phiMin X s) :
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hθ : 0 ≤ theta X s 1 := aux_a3re_theta_nonneg X hn hM s hs
  have hκ2pos : 0 < phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s := sub_pos.mpr hA3
  refine ⟨Real.sqrt_pos.mpr hκ2pos, ?_⟩
  intro J0 hJ0 δ _ hcone
  set a := restrict δ J0 with ha_def
  set b := restrict δ J0ᶜ with hb_def
  set L := ∑ j ∈ J0, δ j ^ 2 with hL
  have hLnn : 0 ≤ L := by positivity
  have hL_eq : ∑ j, a j ^ 2 = L := by
    rw [hL]; simp [a, restrict, ite_pow, Finset.sum_ite_mem]
  have hl2 : l2On δ J0 = Real.sqrt L := rfl
  have haJ : ∀ j, j ∉ J0 → a j = 0 := by
    intro j hj; simp [a, restrict, hj]
  by_cases ha0 : a = 0
  · have : L = 0 := by rw [← hL_eq, ha0]; simp
    rw [hl2, this, Real.sqrt_zero, mul_zero]
    exact Real.sqrt_nonneg _
  have hLpos : 0 < L := by rw [← hL_eq]; exact aux_a3re_sum_sq_pos a ha0
  have hδ : δ = a + b := by
    funext j
    by_cases hj : j ∈ J0 <;> simp [a, b, restrict, hj]
  have hXδ : ∀ i, X.mulVec δ i = X.mulVec a i + X.mulVec b i := by
    intro i; rw [hδ, Matrix.mulVec_add]; rfl
  -- restricted eigenvalue bound
  have hphi : n * phiMin X s * L ≤ ∑ i, (X.mulVec a i) ^ 2 := by
    have h1 : 1 ≤ sparsity a := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp ha0
      exact Finset.card_pos.mpr ⟨j, by simpa [supp] using hj⟩
    have h2 : sparsity a ≤ s := by
      refine le_trans (Finset.card_le_card ?_) hJ0
      intro j hj
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hjn
      exact hj (haJ j hjn)
    have hmem : gramQuad X a / ∑ j, a j ^ 2 ∈ rayleighSet X s := ⟨a, h1, h2, rfl⟩
    have hbdd : BddBelow (rayleighSet X s) := by
      refine ⟨0, ?_⟩
      rintro q ⟨x, _, _, rfl⟩
      unfold gramQuad
      positivity
    have := csInf_le hbdd hmem
    rw [hL_eq] at this
    unfold gramQuad at this
    change phiMin X s ≤ _ at this
    rw [le_div_iff₀ hLpos] at this
    calc (n : ℝ) * phiMin X s * L = n * (phiMin X s * L) := by ring
      _ ≤ n * (1 / n * ∑ i, (X.mulVec a i) ^ 2) := mul_le_mul_of_nonneg_left this hnpos.le
      _ = ∑ i, (X.mulVec a i) ^ 2 := by field_simp
  -- l1 ≤ √s l2 on J0
  have hl1 : l1On δ J0 ≤ Real.sqrt s * Real.sqrt L := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg s)]
    apply Real.le_sqrt_of_sq_le
    unfold l1On
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq J0 (fun j => |δ j|) (fun _ => (1:ℝ))
    simp only [mul_one, sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
    have hc : (J0.card : ℝ) ≤ s := by exact_mod_cast hJ0
    calc (∑ j ∈ J0, |δ j|) ^ 2 ≤ L * J0.card := hcs
      _ ≤ L * s := mul_le_mul_of_nonneg_left hc hLnn
      _ = s * L := by ring
  -- l1 of b
  have hb1 : ∑ k, |b k| = l1On δ J0ᶜ := by
    simp only [b, restrict, l1On, apply_ite abs, abs_zero, Finset.sum_ite_mem, Finset.univ_inter]
  -- cross term
  have hcross : -(n * theta X s 1 * (c0 * (Real.sqrt s * Real.sqrt L)) * Real.sqrt L) ≤
      ∑ i, X.mulVec a i * X.mulVec b i := by
    rw [aux_a3re_bilin X (X.mulVec a) b]
    have hterm : ∀ k, -(|b k| * (n * theta X s 1 * Real.sqrt L)) ≤
        b k * ∑ i, X.mulVec a i * X i k := by
      intro k
      by_cases hk : k ∈ J0
      · have : b k = 0 := by simp [b, restrict, hk]
        simp [this]
      · have hg := aux_a3re_cross X hn s J0 hJ0 a haJ ha0 k hk
        rw [hL_eq] at hg
        have h3 := neg_abs_le (b k * ∑ i, X.mulVec a i * X i k)
        rw [abs_mul] at h3
        have h4 : |b k| * |∑ i, X.mulVec a i * X i k| ≤ |b k| * (n * theta X s 1 * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg _)
        linarith
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hb1] at hsum
    have hK : 0 ≤ (n : ℝ) * theta X s 1 * Real.sqrt L := by positivity
    have h5 : l1On δ J0ᶜ ≤ c0 * (Real.sqrt s * Real.sqrt L) :=
      le_trans hcone (mul_le_mul_of_nonneg_left hl1 hc0.le)
    have h6 := mul_le_mul_of_nonneg_right h5 hK
    nlinarith
  -- conclusion
  unfold euclNorm
  rw [hl2]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, mul_pow, Real.sq_sqrt hκ2pos.le, Real.sq_sqrt (Nat.cast_nonneg _),
    Real.sq_sqrt hLnn]
  have hQ : ∑ i, (X.mulVec δ i) ^ 2 = ∑ i, (X.mulVec a i) ^ 2 +
      2 * ∑ i, X.mulVec a i * X.mulVec b i + ∑ i, (X.mulVec b i) ^ 2 := by
    simp only [hXδ, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hb2 : 0 ≤ ∑ i, (X.mulVec b i) ^ 2 := by positivity
  have hsLL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnn
  rw [hQ]
  have hcross' : -(n * theta X s 1 * c0 * Real.sqrt s * L) ≤
      ∑ i, X.mulVec a i * X.mulVec b i := by
    have : n * theta X s 1 * (c0 * (Real.sqrt s * Real.sqrt L)) * Real.sqrt L =
        n * theta X s 1 * c0 * Real.sqrt s * (Real.sqrt L * Real.sqrt L) := by ring
    rw [this, hsLL] at hcross
    exact hcross
  nlinarith
