-- Prove2me | solution 1 for InputSparsity.Embed.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:37:44.347708+00:00
-- url     : https://prove2.me/submissions/fdaa9099-6fb5-4cf3-b160-afea6e77b0d1

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

open Matrix

namespace Aux_InputSparsity_Embed_lemma_2

open InputSparsity.Embed

theorem exp_quad (x : ℝ) (h0 : 0 ≤ x) (h2 : x ≤ 2) : Real.exp x ≤ 1 + x + 3 / 2 * x ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y, y = x / 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ 1 := by rw [hy]; linarith
  have key : Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3 := by
    have := Real.exp_bound' hy0 hy1 (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hB : 0 ≤ 1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3 := by positivity
  have hsq : Real.exp y * Real.exp y ≤
      (1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3) * (1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3) :=
    mul_le_mul key key (Real.exp_pos y).le hB
  have hexp : (1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3) * (1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3)
      = 1 + 2 * y + 2 * y ^ 2 + 13 / 9 * y ^ 3 + 25 / 36 * y ^ 4 + 2 / 9 * y ^ 5
        + 4 / 81 * y ^ 6 := by ring
  have h3 : y ^ 3 ≤ y ^ 2 := pow_le_pow_of_le_one hy0 hy1 (by norm_num)
  have h4 : y ^ 4 ≤ y ^ 2 := pow_le_pow_of_le_one hy0 hy1 (by norm_num)
  have h5 : y ^ 5 ≤ y ^ 2 := pow_le_pow_of_le_one hy0 hy1 (by norm_num)
  have h6 : y ^ 6 ≤ y ^ 2 := pow_le_pow_of_le_one hy0 hy1 (by norm_num)
  have hx : x = y + y := by rw [hy]; ring
  rw [hx, Real.exp_add]
  nlinarith

theorem lev_nonneg {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (i : Fin n) : 0 ≤ lev U i :=
  Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem lev_sum {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) :
    ∑ i, lev U i = r := by
  unfold lev
  rw [Finset.sum_comm]
  have hcol : ∀ j, ∑ i, U i j ^ 2 = 1 := by
    intro j
    have h := congrFun (congrFun hU j) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp [hcol]

noncomputable def gfac {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T θ : ℝ) (j : Fin t)
    (i : Fin n) (a : Fin t) : ℝ :=
  if a = j ∧ lev U i ≤ T then Real.exp (θ * lev U i) else 1

noncomputable def zz {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T θ : ℝ) (i : Fin n) : ℝ :=
  if lev U i ≤ T then Real.exp (θ * lev U i) - 1 else 0

theorem sum_gfac {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T θ : ℝ) (j : Fin t) (i : Fin n) :
    ∑ a, gfac U T θ j i a = t + zz U T θ i := by
  have hsplit : ∀ a : Fin t, gfac U T θ j i a = 1 + (if a = j then zz U T θ i else 0) := by
    intro a
    unfold gfac zz
    by_cases ha : a = j <;> by_cases hc : lev U i ≤ T <;> simp [ha, hc]
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem zz_nonneg {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T θ : ℝ) (hθ : 0 ≤ θ) (i : Fin n) :
    0 ≤ zz U T θ i := by
  unfold zz
  split_ifs
  · have : 1 ≤ Real.exp (θ * lev U i) :=
      Real.one_le_exp (mul_nonneg hθ (lev_nonneg U i))
    linarith
  · exact le_rfl

theorem exp_X {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T θ : ℝ) (j : Fin t)
    (h : Fin n → Fin t) :
    Real.exp (θ * ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)
      = ∏ i, gfac U T θ j i (h i) := by
  rw [Finset.mul_sum, Real.exp_sum, Finset.prod_filter]
  rfl

end Aux_InputSparsity_Embed_lemma_2

open InputSparsity.Embed Aux_InputSparsity_Embed_lemma_2 in
theorem solution {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) (ht : 0 < t)
    (T δh : ℝ) (hT : 0 < T) (hδh : 0 < δh)
    (hsize : 6 * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T),
        (lev U i) ^ 2) /
        (T ^ 2 * Real.log ((t : ℝ) / δh)) ≤ (t : ℝ)) :
    1 - δh ≤ unifProb (Fin n → Fin t)
      {h | BucketBound U T (T * Real.log ((t : ℝ) / δh) + (r : ℝ) / t) h} := by
  classical
  have hprob_nonneg : 0 ≤ unifProb (Fin n → Fin t)
      {h | BucketBound U T (T * Real.log ((t : ℝ) / δh) + (r : ℝ) / t) h} := by
    unfold unifProb
    positivity
  by_cases hδ1 : 1 ≤ δh
  · linarith
  push_neg at hδ1
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log ((t : ℝ) / δh) := ⟨_, rfl⟩
  rw [← hL] at hsize ⊢
  have hLpos : 0 < L := by
    rw [hL]
    apply Real.log_pos
    rw [lt_div_iff₀ hδh]
    linarith
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), (lev U i) ^ 2 :=
    ⟨_, rfl⟩
  rw [← hS] at hsize
  have hSt : S / t ≤ T ^ 2 * L / 6 := by
    have hden : 0 < T ^ 2 * L := by positivity
    rw [div_le_iff₀ hden] at hsize
    rw [div_le_iff₀ htpos]
    nlinarith
  obtain ⟨W, hW⟩ : ∃ W, W = T * L + (r : ℝ) / t := ⟨_, rfl⟩
  rw [← hW]
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = 2 / T := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have htne : (t : ℝ) ≠ 0 := htpos.ne'
  have hθT : θ * T = 2 := by rw [hθ, div_mul_cancel₀ 2 hT.ne']
  -- bound on the sum of the zz terms
  have hzz_le : ∀ i, zz U T θ i ≤
      (if lev U i ≤ T then θ * lev U i + 3 / 2 * θ ^ 2 * (lev U i) ^ 2 else 0) := by
    intro i
    unfold zz
    split_ifs with hc
    · have hx0 : 0 ≤ θ * lev U i := mul_nonneg hθ0 (lev_nonneg U i)
      have hx2 : θ * lev U i ≤ 2 := by
        rw [← hθT]
        exact mul_le_mul_of_nonneg_left hc hθ0
      have := exp_quad (θ * lev U i) hx0 hx2
      nlinarith
    · exact le_rfl
  have hlight : ∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i ≤ r := by
    rw [← lev_sum U hU]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => lev_nonneg U i)
  have hzsum : (∑ i, zz U T θ i) / t ≤ θ * r / t + L := by
    have h1 : ∑ i, zz U T θ i ≤
        θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i) + 3 / 2 * θ ^ 2 * S := by
      calc ∑ i, zz U T θ i
          ≤ ∑ i, (if lev U i ≤ T then θ * lev U i + 3 / 2 * θ ^ 2 * (lev U i) ^ 2 else 0) :=
            Finset.sum_le_sum (fun i _ => hzz_le i)
        _ = θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i)
              + 3 / 2 * θ ^ 2 * S := by
            rw [← Finset.sum_filter, Finset.sum_add_distrib, hS, Finset.mul_sum, Finset.mul_sum]
    have h2 : θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i) ≤ θ * r :=
      mul_le_mul_of_nonneg_left hlight hθ0
    have h3 : 3 / 2 * θ ^ 2 * S / t ≤ L := by
      have hθ2 : θ ^ 2 * T ^ 2 = 4 := by rw [← mul_pow, hθT]; norm_num
      have : 3 / 2 * θ ^ 2 * S / t = 3 / 2 * θ ^ 2 * (S / t) := by ring
      rw [this]
      have hθsq : 0 ≤ 3 / 2 * θ ^ 2 := by positivity
      calc 3 / 2 * θ ^ 2 * (S / t) ≤ 3 / 2 * θ ^ 2 * (T ^ 2 * L / 6) :=
            mul_le_mul_of_nonneg_left hSt hθsq
        _ = (θ ^ 2 * T ^ 2) * L / 4 := by ring
        _ = L := by rw [hθ2]; ring
    have h4 : (∑ i, zz U T θ i) / t ≤
        (θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i)
          + 3 / 2 * θ ^ 2 * S) / t :=
      div_le_div_of_nonneg_right h1 htpos.le
    have h5 : (θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i)
          + 3 / 2 * θ ^ 2 * S) / t
        = θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i) / t
          + 3 / 2 * θ ^ 2 * S / t := by ring
    have h6 : θ * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T), lev U i) / t ≤ θ * r / t :=
      div_le_div_of_nonneg_right h2 htpos.le
    linarith
  -- moment generating bound for one bucket
  have hmgf : ∀ j : Fin t,
      ∑ h : Fin n → Fin t,
        Real.exp (θ * ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)
      ≤ (t : ℝ) ^ n * Real.exp (θ * r / t + L) := by
    intro j
    simp only [exp_X]
    rw [← Fintype.prod_sum (fun i a => gfac U T θ j i a)]
    simp only [sum_gfac]
    have hfac : ∀ i, (t : ℝ) + zz U T θ i ≤ t * Real.exp (zz U T θ i / t) := by
      intro i
      have := Real.add_one_le_exp (zz U T θ i / t)
      have e : (t : ℝ) + zz U T θ i = t * (zz U T θ i / t + 1) := by
        rw [mul_add, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ htne]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left this htpos.le
    calc ∏ i, ((t : ℝ) + zz U T θ i) ≤ ∏ i, ((t : ℝ) * Real.exp (zz U T θ i / t)) :=
          Finset.prod_le_prod (fun i _ => by
            have := zz_nonneg U T θ hθ0 i
            linarith) (fun i _ => hfac i)
      _ = (t : ℝ) ^ n * Real.exp ((∑ i, zz U T θ i) / t) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, Finset.sum_div]
      _ ≤ (t : ℝ) ^ n * Real.exp (θ * r / t + L) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzsum) (by positivity)
  -- bad set of one bucket
  have hbad : ∀ j : Fin t,
      ((Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)).card : ℝ)
        ≤ (t : ℝ) ^ n * (δh / t) := by
    intro j
    have hcount : ((Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)).card : ℝ)
        ≤ ∑ h : Fin n → Fin t, Real.exp (-(θ * W)) *
          Real.exp (θ * ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      calc ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin t =>
              W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i), (1 : ℝ)
          ≤ ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin t =>
              W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i),
              Real.exp (-(θ * W)) * Real.exp
                (θ * ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i) := by
            apply Finset.sum_le_sum
            intro h hh
            rw [Finset.mem_filter] at hh
            rw [← Real.exp_add]
            apply Real.one_le_exp
            have := mul_le_mul_of_nonneg_left hh.2.le hθ0
            linarith
        _ ≤ ∑ h : Fin n → Fin t, Real.exp (-(θ * W)) * Real.exp
              (θ * ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun h _ _ => by positivity)
    rw [← Finset.mul_sum] at hcount
    have hm := mul_le_mul_of_nonneg_left (hmgf j) (Real.exp_pos (-(θ * W))).le
    have hval : Real.exp (-(θ * W)) * ((t : ℝ) ^ n * Real.exp (θ * r / t + L))
        = (t : ℝ) ^ n * (δh / t) := by
      rw [mul_left_comm, ← Real.exp_add]
      have e1 : -(θ * W) + (θ * r / t + L) = -L := by
        rw [hW]
        have : θ * (T * L) = 2 * L := by rw [← mul_assoc, hθT]
        linear_combination (-1 : ℝ) * this
      rw [e1, Real.exp_neg, hL, Real.exp_log (show (0 : ℝ) < t / δh by positivity), inv_div]
    linarith
  -- union bound
  have hcardU : (Finset.univ : Finset (Fin n → Fin t)).card = t ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Fin t))) (fun h => BucketBound U T W h)
  have hsub : (Finset.univ.filter (fun h : Fin n → Fin t => ¬ BucketBound U T W h)) ⊆
      Finset.univ.biUnion (fun j : Fin t => Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)) := by
    intro h hh
    rw [Finset.mem_filter] at hh
    have hh2 := hh.2
    unfold BucketBound at hh2
    push_neg at hh2
    obtain ⟨j, hj⟩ := hh2
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hbadcard : ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ BucketBound U T W h)).card : ℝ)
      ≤ (t : ℝ) ^ n * δh := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin t)))
      (t := fun j : Fin t => Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i))
    have h3 : ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ BucketBound U T W h)).card : ℝ)
        ≤ ∑ j : Fin t, ((Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast le_trans h1 h2
    calc ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ BucketBound U T W h)).card : ℝ)
        ≤ ∑ j : Fin t, ((Finset.univ.filter (fun h : Fin n → Fin t =>
          W < ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i)).card : ℝ) := h3
      _ ≤ ∑ _j : Fin t, (t : ℝ) ^ n * (δh / t) := Finset.sum_le_sum (fun j _ => hbad j)
      _ = (t : ℝ) ^ n * δh := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          first
            | (field_simp; ring1)
            | field_simp
  have hgood : (1 - δh) * (t : ℝ) ^ n ≤
      ((Finset.univ.filter (fun h : Fin n → Fin t => BucketBound U T W h)).card : ℝ) := by
    have hs : ((Finset.univ.filter (fun h : Fin n → Fin t => BucketBound U T W h)).card : ℝ) +
        ((Finset.univ.filter (fun h : Fin n → Fin t => ¬ BucketBound U T W h)).card : ℝ)
        = (t : ℝ) ^ n := by
      rw [← Nat.cast_add, hsplit, hcardU, Nat.cast_pow]
    nlinarith
  unfold unifProb
  rw [Nat.card_eq_card_toFinset, Set.toFinset_setOf, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  push_cast
  rw [le_div_iff₀ (show (0 : ℝ) < (t : ℝ) ^ n by positivity)]
  exact hgood
