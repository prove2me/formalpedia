-- Prove2me | solution 1 for InputSparsity.Embed.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:54:20.793075+00:00
-- url     : https://prove2.me/submissions/4889bb0a-a8c3-41d7-a66e-145c3d083c0f

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

open Matrix

namespace Aux_InputSparsity_Embed_lemma_6

open InputSparsity.Embed

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem sgn_xnor (a b : Bool) : sgn (a == b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn]

theorem sketch_entry {n t : ℕ} (h : Fin n → Fin t) (σ : Fin n → Bool) (a : Fin t) (i : Fin n) :
    sketch h σ a i = if h i = a then sgn (σ i) else 0 := by
  unfold sketch Dmat
  rw [Matrix.mul_diagonal]
  simp only [Phi]
  split_ifs <;> simp

theorem sketch_coord {n t : ℕ} (h : Fin n → Fin t) (σ : Fin n → Bool) (x : Fin n → ℝ)
    (a : Fin t) :
    (sketch h σ *ᵥ x) a = ∑ i, (if h i = a then sgn (σ i) * x i else 0) := by
  simp only [Matrix.mulVec, dotProduct, sketch_entry]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem sqNorm_eq_dot {m : ℕ} (w : Fin m → ℝ) : sqNorm w = w ⬝ᵥ w := by
  unfold sqNorm dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ysq_le_lev {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U)
    (y : Fin n → ℝ) (hy : y ∈ LinearMap.range (Matrix.mulVecLin U)) (hy1 : sqNorm y = 1)
    (j : Fin n) : y j ^ 2 ≤ lev U j := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
  rw [Matrix.mulVecLin_apply] at hx
  have hU' : Uᵀ * U = 1 := hU
  have hn : sqNorm (U *ᵥ x) = sqNorm x := by
    rw [sqNorm_eq_dot, sqNorm_eq_dot, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]
  rw [hx, hy1] at hn
  have hyj : y j = ∑ k, U j k * x k := by
    rw [← hx]
    simp only [Matrix.mulVec, dotProduct]
  rw [hyj]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (U j) x
  have hx1 : ∑ k, x k ^ 2 = 1 := hn.symm
  unfold lev
  rw [hx1, mul_one] at hcs
  exact hcs

theorem sq_sum_single {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i i', f i ≠ 0 → f i' ≠ 0 → i = i') :
    (∑ i, f i) ^ 2 = ∑ i, f i ^ 2 := by
  by_cases hex : ∃ i0, f i0 ≠ 0
  · obtain ⟨i0, hi0⟩ := hex
    have hz : ∀ i, i ≠ i0 → f i = 0 := by
      intro i hne
      by_contra hc
      exact hne (hf i i0 hc hi0)
    rw [Finset.sum_eq_single i0 (fun i _ hne => hz i hne) (fun h => absurd (Finset.mem_univ i0) h),
      Finset.sum_eq_single i0 (fun i _ hne => by rw [hz i hne]; ring)
        (fun h => absurd (Finset.mem_univ i0) h)]
  · push_neg at hex
    simp [hex]

noncomputable def bpart {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (σ : Fin n → Bool) (j : Fin n) : Bool :=
  decide (∃ i, h i = h j ∧ T < lev U i ∧ σ i = true)

noncomputable def tau {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (σ : Fin n → Bool) : Fin n → Bool :=
  fun j => if lev U j ≤ T then (σ j == bpart U T h σ j) else σ j

theorem tau_heavy {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (σ : Fin n → Bool) (i : Fin n) (hi : T < lev U i) : tau U T h σ i = σ i := by
  simp only [tau, if_neg (not_le.mpr hi)]

theorem bpart_tau {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (σ : Fin n → Bool) (j : Fin n) : bpart U T h (tau U T h σ) j = bpart U T h σ j := by
  unfold bpart
  rw [decide_eq_decide]
  constructor
  · rintro ⟨i, h1, h2, h3⟩
    refine ⟨i, h1, h2, ?_⟩
    rw [← tau_heavy U T h σ i h2]
    exact h3
  · rintro ⟨i, h1, h2, h3⟩
    refine ⟨i, h1, h2, ?_⟩
    rw [tau_heavy U T h σ i h2]
    exact h3

theorem tau_tau {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (σ : Fin n → Bool) : tau U T h (tau U T h σ) = σ := by
  funext j
  show (if lev U j ≤ T then (tau U T h σ j == bpart U T h (tau U T h σ) j)
    else tau U T h σ j) = σ j
  rw [bpart_tau]
  by_cases hj : lev U j ≤ T
  · rw [if_pos hj]
    have e : tau U T h σ j = (σ j == bpart U T h σ j) := by simp only [tau, if_pos hj]
    rw [e]
    generalize σ j = x
    generalize bpart U T h σ j = z
    cases x <;> cases z <;> rfl
  · rw [if_neg hj]
    simp only [tau, if_neg hj]

noncomputable def Hj {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (y : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if h i = h j ∧ T < lev U i then y i else 0

noncomputable def cc {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (y : Fin n → ℝ) (j : Fin n) : ℝ :=
  if lev U j ≤ T then y j * ∑ i, Hj U T h y i j else 0

theorem Hj_single {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (hP : PerfectOnHeavy U T h) (y : Fin n → ℝ) (j : Fin n) :
    ∀ i i', Hj U T h y i j ≠ 0 → Hj U T h y i' j ≠ 0 → i = i' := by
  intro i i' hi hi'
  have c1 : h i = h j ∧ T < lev U i := by
    by_contra hc
    unfold Hj at hi
    rw [if_neg hc] at hi
    exact hi rfl
  have c2 : h i' = h j ∧ T < lev U i' := by
    by_contra hc
    unfold Hj at hi'
    rw [if_neg hc] at hi'
    exact hi' rfl
  by_contra hne
  exact hP i i' c1.2 c2.2 hne (by rw [c1.1, c2.1])

theorem cross_pt {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (hP : PerfectOnHeavy U T h) (σ : Fin n → Bool) (y : Fin n → ℝ) (j : Fin n) :
    (∑ i, (if h i = h j then sgn (σ i) * heavy U T y i else 0)) *
      (sgn (σ j) * light U T y j) = sgn (tau U T h σ j) * cc U T h y j := by
  have hG : ∑ i, (if h i = h j then sgn (σ i) * heavy U T y i else 0)
      = ∑ i, sgn (σ i) * Hj U T h y i j := by
    apply Finset.sum_congr rfl
    intro i _
    unfold heavy Hj
    by_cases h1 : h i = h j <;> by_cases h2 : T < lev U i <;> simp [h1, h2]
  by_cases hl : lev U j ≤ T
  · have hlj : light U T y j = y j := by simp [light, hl]
    have htau : tau U T h σ j = (σ j == bpart U T h σ j) := by simp only [tau, if_pos hl]
    rw [hG, hlj, htau, sgn_xnor]
    unfold cc
    rw [if_pos hl]
    by_cases hex : ∃ i0, Hj U T h y i0 j ≠ 0
    · obtain ⟨i0, hi0⟩ := hex
      have hcond : h i0 = h j ∧ T < lev U i0 := by
        by_contra hc
        unfold Hj at hi0
        rw [if_neg hc] at hi0
        exact hi0 rfl
      have uniq : ∀ i, h i = h j ∧ T < lev U i → i = i0 := by
        intro i hi
        by_contra hne
        exact hP i i0 hi.2 hcond.2 hne (by rw [hi.1, hcond.1])
      have hzero : ∀ i, i ≠ i0 → Hj U T h y i j = 0 := by
        intro i hne
        unfold Hj
        rw [if_neg]
        intro hi
        exact hne (uniq i hi)
      have hs1 : ∑ i, sgn (σ i) * Hj U T h y i j = sgn (σ i0) * Hj U T h y i0 j :=
        Finset.sum_eq_single i0 (fun i _ hne => by rw [hzero i hne, mul_zero])
          (fun hh => absurd (Finset.mem_univ i0) hh)
      have hs2 : ∑ i, Hj U T h y i j = Hj U T h y i0 j :=
        Finset.sum_eq_single i0 (fun i _ hne => hzero i hne)
          (fun hh => absurd (Finset.mem_univ i0) hh)
      have hb : bpart U T h σ j = σ i0 := by
        unfold bpart
        rw [Bool.eq_iff_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨i, h1, h2, h3⟩
          have := uniq i ⟨h1, h2⟩
          rw [← this]
          exact h3
        · intro hs
          exact ⟨i0, hcond.1, hcond.2, hs⟩
      rw [hs1, hs2, hb]
      ring
    · push_neg at hex
      have hs1 : ∑ i, sgn (σ i) * Hj U T h y i j = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [hex i, mul_zero])
      have hs2 : ∑ i, Hj U T h y i j = 0 := Finset.sum_eq_zero (fun i _ => hex i)
      rw [hs1, hs2]
      ring
  · have hlj : light U T y j = 0 := by simp [light, hl]
    unfold cc
    rw [if_neg hl, hlj]
    ring

theorem cross_eq {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ) (h : Fin n → Fin t)
    (hP : PerfectOnHeavy U T h) (σ : Fin n → Bool) (y : Fin n → ℝ) :
    (sketch h σ *ᵥ heavy U T y) ⬝ᵥ (sketch h σ *ᵥ light U T y)
      = ∑ j, sgn (tau U T h σ j) * cc U T h y j := by
  simp only [dotProduct, sketch_coord, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← cross_pt U T h hP σ y j]
  rw [Finset.sum_eq_single (h j)]
  · rw [if_pos rfl]
  · intro a _ ha
    rw [if_neg (fun e => ha e.symm), mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem V_le {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) (T W : ℝ)
    (h : Fin n → Fin t) (hB : BucketBound U T W h) (hP : PerfectOnHeavy U T h)
    (y : Fin n → ℝ) (hy : y ∈ LinearMap.range (Matrix.mulVecLin U)) (hy1 : sqNorm y = 1) :
    ∑ j, cc U T h y j ^ 2 ≤ W := by
  have hlev := ysq_le_lev U hU y hy hy1
  have hA : ∀ j, cc U T h y j ^ 2 ≤ ∑ i, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i
      then y j ^ 2 * y i ^ 2 else 0) := by
    intro j
    by_cases hl : lev U j ≤ T
    · unfold cc
      rw [if_pos hl, mul_pow, sq_sum_single _ (Hj_single U T h hP y j), Finset.mul_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      unfold Hj
      by_cases h1 : h i = h j <;> by_cases h2 : T < lev U i <;> simp [h1, h2, hl]
    · unfold cc
      rw [if_neg hl]
      have : ∑ i, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0) = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [if_neg (fun hc => hl hc.1)])
      rw [this]
      norm_num
  have hB' : ∀ i, ∑ j, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0)
      ≤ W * y i ^ 2 := by
    intro i
    have hpt : ∀ j, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0)
        ≤ y i ^ 2 * (if h j = h i ∧ lev U j ≤ T then lev U j else 0) := by
      intro j
      by_cases hc : lev U j ≤ T ∧ h i = h j ∧ T < lev U i
      · rw [if_pos hc, if_pos ⟨hc.2.1.symm, hc.1⟩]
        have := hlev j
        have hyi : 0 ≤ y i ^ 2 := sq_nonneg _
        nlinarith
      · rw [if_neg hc]
        apply mul_nonneg (sq_nonneg _)
        split_ifs
        · exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
        · exact le_rfl
    have hbk := hB (h i)
    rw [Finset.sum_filter] at hbk
    calc ∑ j, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0)
        ≤ ∑ j, y i ^ 2 * (if h j = h i ∧ lev U j ≤ T then lev U j else 0) :=
          Finset.sum_le_sum (fun j _ => hpt j)
      _ = y i ^ 2 * ∑ j, (if h j = h i ∧ lev U j ≤ T then lev U j else 0) := by
          rw [Finset.mul_sum]
      _ ≤ y i ^ 2 * W := mul_le_mul_of_nonneg_left hbk (sq_nonneg _)
      _ = W * y i ^ 2 := by ring
  calc ∑ j, cc U T h y j ^ 2
      ≤ ∑ j, ∑ i, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0) :=
        Finset.sum_le_sum (fun j _ => hA j)
    _ = ∑ i, ∑ j, (if lev U j ≤ T ∧ h i = h j ∧ T < lev U i then y j ^ 2 * y i ^ 2 else 0) :=
        Finset.sum_comm
    _ ≤ ∑ i, W * y i ^ 2 := Finset.sum_le_sum (fun i _ => hB' i)
    _ = W := by
        rw [← Finset.mul_sum]
        unfold sqNorm at hy1
        rw [hy1, mul_one]

theorem hoeff_one {n : ℕ} (c : Fin n → ℝ) (lam thr : ℝ) (hlam : 0 ≤ lam) :
    ((Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j)).card : ℝ)
      ≤ 2 ^ n * Real.exp (-(lam * thr) + lam ^ 2 * (∑ j, c j ^ 2) / 2) := by
  have hprod : ∀ ρ : Fin n → Bool, Real.exp (lam * ∑ j, sgn (ρ j) * c j)
      = ∏ j, Real.exp (lam * sgn (ρ j) * c j) := by
    intro ρ
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_assoc]
  have hsum : ∑ ρ : Fin n → Bool, ∏ j, Real.exp (lam * sgn (ρ j) * c j)
      = ∏ j, (Real.exp (lam * c j) + Real.exp (-(lam * c j))) := by
    rw [← Fintype.prod_sum (fun j b => Real.exp (lam * sgn b * c j))]
    apply Finset.prod_congr rfl
    intro j _
    rw [Fintype.sum_bool]
    simp [sgn]
  have hcosh : ∏ j, (Real.exp (lam * c j) + Real.exp (-(lam * c j)))
      ≤ 2 ^ n * Real.exp (lam ^ 2 * (∑ j, c j ^ 2) / 2) := by
    calc ∏ j, (Real.exp (lam * c j) + Real.exp (-(lam * c j)))
        ≤ ∏ j, (2 * Real.exp ((lam * c j) ^ 2 / 2)) := by
          apply Finset.prod_le_prod
          · intro j _
            positivity
          · intro j _
            have := Real.cosh_le_exp_half_sq (lam * c j)
            rw [Real.cosh_eq] at this
            linarith
      _ = 2 ^ n * Real.exp (lam ^ 2 * (∑ j, c j ^ 2) / 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, Finset.mul_sum, Finset.sum_div]
          congr 2
          apply Finset.sum_congr rfl
          intro j _
          ring
  calc ((Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j)).card : ℝ)
      = ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j), (1 : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    _ ≤ ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j),
          Real.exp (-(lam * thr)) * Real.exp (lam * ∑ j, sgn (ρ j) * c j) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have := mul_le_mul_of_nonneg_left hρ.2.le hlam
        linarith
    _ ≤ ∑ ρ : Fin n → Bool, Real.exp (-(lam * thr)) * Real.exp (lam * ∑ j, sgn (ρ j) * c j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ρ _ _ => by positivity)
    _ = Real.exp (-(lam * thr)) * ∏ j, (Real.exp (lam * c j) + Real.exp (-(lam * c j))) := by
        rw [← Finset.mul_sum]
        simp only [hprod]
        rw [hsum]
    _ ≤ Real.exp (-(lam * thr)) * (2 ^ n * Real.exp (lam ^ 2 * (∑ j, c j ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = 2 ^ n * Real.exp (-(lam * thr) + lam ^ 2 * (∑ j, c j ^ 2) / 2) := by
        rw [Real.exp_add]
        ring

theorem hoeff_abs {n : ℕ} (c : Fin n → ℝ) (lam thr : ℝ) (hlam : 0 ≤ lam) :
    ((Finset.univ.filter (fun ρ : Fin n → Bool => thr < |∑ j, sgn (ρ j) * c j|)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(lam * thr) + lam ^ 2 * (∑ j, c j ^ 2) / 2)) := by
  have hsub : Finset.univ.filter (fun ρ : Fin n → Bool => thr < |∑ j, sgn (ρ j) * c j|) ⊆
      Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j) ∪
      Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * (fun k => -c k) j) := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases lt_abs.mp hρ.2 with h1 | h1
    · exact Or.inl ⟨Finset.mem_univ _, h1⟩
    · right
      refine ⟨Finset.mem_univ _, ?_⟩
      have e : ∑ j, sgn (ρ j) * (fun k => -c k) j = -∑ j, sgn (ρ j) * c j := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [e]
      exact h1
  have h1 := hoeff_one c lam thr hlam
  have h2 := hoeff_one (fun k => -c k) lam thr hlam
  have hsq : ∑ j, (fun k => -c k) j ^ 2 = ∑ j, c j ^ 2 :=
    Finset.sum_congr rfl (fun j _ => neg_sq (c j))
  rw [hsq] at h2
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_union_le
    (Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j))
    (Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * (fun k => -c k) j))
  have h5 : ((Finset.univ.filter (fun ρ : Fin n → Bool => thr < |∑ j, sgn (ρ j) * c j|)).card : ℝ)
      ≤ ((Finset.univ.filter (fun ρ : Fin n → Bool => thr < ∑ j, sgn (ρ j) * c j)).card : ℝ) +
        ((Finset.univ.filter (fun ρ : Fin n → Bool =>
          thr < ∑ j, sgn (ρ j) * (fun k => -c k) j)).card : ℝ) := by
    exact_mod_cast le_trans h3 h4
  linarith

end Aux_InputSparsity_Embed_lemma_6

open InputSparsity.Embed Aux_InputSparsity_Embed_lemma_6 in
theorem solution :
    ∃ KC : ℝ, 0 < KC ∧
      ∀ {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ),
        HasOrthonormalCols U →
        ∀ (T W : ℝ), 0 < T → 0 < W →
        ∀ (h : Fin n → Fin t), BucketBound U T W h →
          PerfectOnHeavy U T h →
        ∀ (y : Fin n → ℝ),
          y ∈ LinearMap.range (Matrix.mulVecLin U) → sqNorm y = 1 →
          ∀ δC : ℝ, 0 < δC → δC ≤ Real.exp (-1) →
            unifProb (Fin n → Bool)
              {σ | KC * Real.sqrt (W * Real.log (1 / δC)) <
                |(sketch h σ *ᵥ heavy U T y) ⬝ᵥ
                  (sketch h σ *ᵥ light U T y)|} ≤ δC := by
  refine ⟨2, by norm_num, ?_⟩
  intro n r t U hU T W hT hW h hB hP y hy hy1 δC hδ hδe
  classical
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (1 / δC) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (show (0 : ℝ) < 1 / δC by positivity), one_div]
    rw [Real.exp_neg] at hδe
    exact (le_inv_comm₀ hδ (Real.exp_pos 1)).mp hδe
  have hexpL : Real.exp (-L) = δC := by
    rw [Real.exp_neg, hL, Real.exp_log (show (0 : ℝ) < 1 / δC by positivity), one_div, inv_inv]
  have hδhalf : δC ≤ 1 / 2 := by
    have he : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div,
        div_le_div_iff₀ (Real.exp_pos 1) (show (0 : ℝ) < 2 by norm_num)]
      linarith [Real.exp_one_gt_d9]
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (W * L) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = W * L := by
    rw [hs, Real.sq_sqrt (show (0 : ℝ) ≤ W * L by positivity)]
  rw [← hL, ← hs]
  -- the linear Rademacher sum
  have hV := V_le U hU T W h hB hP y hy hy1
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 2 * s / W := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hcount := hoeff_abs (cc U T h y) lam (2 * s) hlam0
  have hlt : lam * (2 * s) = 4 * L := by
    have e : lam * (2 * s) = 4 * s ^ 2 / W := by rw [hlam]; ring
    rw [e, hs2, mul_div_assoc, mul_div_cancel_left₀ L hW.ne']
  have hlam2 : lam ^ 2 = 4 * L / W := by
    rw [hlam, div_pow, mul_pow, hs2,
      div_eq_div_iff (show (W : ℝ) ^ 2 ≠ 0 by positivity) hW.ne']
    ring
  have hexp_le : -(lam * (2 * s)) + lam ^ 2 * (∑ j, cc U T h y j ^ 2) / 2 ≤ -L + -L := by
    rw [hlt, hlam2]
    have hVW : (∑ j, cc U T h y j ^ 2) / W ≤ 1 := by
      rw [div_le_one hW]
      exact hV
    have e : 4 * L / W * (∑ j, cc U T h y j ^ 2) / 2 = 2 * L * ((∑ j, cc U T h y j ^ 2) / W) := by
      ring
    rw [e]
    have hL0 : 0 ≤ 2 * L := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hVW hL0]
  have hbound : Real.exp (-(lam * (2 * s)) + lam ^ 2 * (∑ j, cc U T h y j ^ 2) / 2)
      ≤ δC * δC := by
    calc Real.exp (-(lam * (2 * s)) + lam ^ 2 * (∑ j, cc U T h y j ^ 2) / 2)
        ≤ Real.exp (-L + -L) := Real.exp_le_exp.mpr hexp_le
      _ = δC * δC := by rw [Real.exp_add, hexpL]
  -- transfer the count through the involution tau
  have hcross : ∀ σ : Fin n → Bool,
      (sketch h σ *ᵥ heavy U T y) ⬝ᵥ (sketch h σ *ᵥ light U T y)
        = ∑ j, sgn (tau U T h σ j) * cc U T h y j := fun σ => cross_eq U T h hP σ y
  have hcardeq : (Finset.univ.filter (fun σ : Fin n → Bool =>
      2 * s < |(sketch h σ *ᵥ heavy U T y) ⬝ᵥ (sketch h σ *ᵥ light U T y)|)).card
      = (Finset.univ.filter (fun ρ : Fin n → Bool =>
          2 * s < |∑ j, sgn (ρ j) * cc U T h y j|)).card := by
    apply Finset.card_bij (fun σ _ => tau U T h σ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hcross σ]
      exact hσ.2
    · intro a _ b _ hab
      have := congrArg (tau U T h) hab
      rwa [tau_tau, tau_tau] at this
    · intro b hb
      refine ⟨tau U T h b, ?_, tau_tau U T h b⟩
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hcross, tau_tau]
      exact hb.2
  unfold unifProb
  rw [Nat.card_eq_card_toFinset, Set.toFinset_setOf, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, hcardeq]
  push_cast
  rw [div_le_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)]
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hδ0 : 0 ≤ δC := hδ.le
  calc ((Finset.univ.filter (fun ρ : Fin n → Bool =>
          2 * s < |∑ j, sgn (ρ j) * cc U T h y j|)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(lam * (2 * s)) + lam ^ 2 * (∑ j, cc U T h y j ^ 2) / 2)) :=
        hcount
    _ ≤ 2 * (2 ^ n * (δC * δC)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound h2n) (by norm_num)
    _ ≤ δC * 2 ^ n := by
        have h2d : 2 * δC * δC ≤ δC := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h2d h2n]
