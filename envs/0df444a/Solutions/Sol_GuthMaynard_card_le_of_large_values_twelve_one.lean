-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values_twelve_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:41:01.478238+00:00
-- url     : https://prove2.me/submissions/7d6b0fb3-3940-4cb9-87ce-67dea25dcb6b

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly_Iterm_pos
import Theorems.Thm_GuthMaynard_norm_S_one_le
import Theorems.Thm_GuthMaynard_norm_S_two_le
import Theorems.Thm_GuthMaynard_norm_S_three_le

/-!
Part A of the Blueprint for Proposition 12.1: the eight-term bound `twelve_one`.
-/

namespace GuthMaynardS1213.P121.PartA

open GuthMaynard Complex

/-! ### Helpers copied from the Theorem 1.1 development -/

lemma exists_weight : ∃ w : ℝ → ℝ, IsWeight w := by
  let f : ContDiffBump (3 / 2 : ℝ) := ⟨3 / 10, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨f, ⟨f.contDiff, fun x => f.nonneg, ?_, ?_⟩⟩
  · rw [f.support_eq]
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have hr : f.rOut = 1 / 2 := rfl
    rw [hr] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma smoothed_eq (w : ℝ → ℝ) (hw : IsWeight w) (M : ℕ) (hM : 0 < M) (A : Finset ℕ)
    (hA : ∀ n ∈ A, M ≤ n ∧ n ≤ 2 * M ∧ 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M) (b : ℕ → ℂ) (t : ℝ) :
    smoothedPoly w M (fun n => if n ∈ A then b n else 0) t =
      ∑ n ∈ A, b n * (n : ℂ) ^ ((t : ℂ) * I) := by
  unfold smoothedPoly
  have hsub : A ⊆ Finset.Icc M (2 * M) := by
    intro n hn
    have := hA n hn
    simp only [Finset.mem_Icc]; exact ⟨this.1, this.2.1⟩
  rw [← Finset.sum_subset hsub (by intro n _ hn; simp [hn])]
  apply Finset.sum_congr rfl
  intro n hn
  have h := hA n hn
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hw1 : w ((n : ℝ) / M) = 1 := by
    apply hw.eq_one
    constructor
    · rw [le_div_iff₀ hMr]
      have : (6 * M : ℝ) ≤ 5 * n := by exact_mod_cast h.2.2.1
      linarith
    · rw [div_le_iff₀ hMr]
      have : (5 * n : ℝ) ≤ 9 * M := by exact_mod_cast h.2.2.2
      linarith
  simp [hn, hw1]

lemma pieces (N : ℕ) (hN : 6 ≤ N) :
    ∃ (M : Fin 3 → ℕ) (A : Fin 3 → Finset ℕ),
      (∀ i, 0 < M i ∧ N ≤ 2 * M i ∧ M i ≤ 2 * N ∧
        ∀ n ∈ A i, M i ≤ n ∧ n ≤ 2 * M i ∧ 6 * M i ≤ 5 * n ∧ 5 * n ≤ 9 * M i) ∧
      ∀ f : ℕ → ℂ, ∑ n ∈ Finset.Icc N (2 * N), f n = ∑ i, ∑ n ∈ A i, f n := by
  refine ⟨![5 * N / 6, N, (10 * N + 8) / 9],
    ![(Finset.Icc N (2 * N)).filter (fun n => 5 * n < 6 * N),
      (Finset.Icc N (2 * N)).filter (fun n => 6 * N ≤ 5 * n ∧ 5 * n ≤ 9 * N),
      (Finset.Icc N (2 * N)).filter (fun n => 9 * N < 5 * n)], ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨by simp; omega, by simp; omega, by simp; omega, ?_⟩
      intro n hn
      simp [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    · refine ⟨by simp; omega, by simp; omega, by simp; omega, ?_⟩
      intro n hn
      simp [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    · refine ⟨by simp; omega, by simp; omega, by simp; omega, ?_⟩
      intro n hn
      simp [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
  · intro f
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have h1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc N (2 * N)) (fun n => 5 * n < 6 * N) f
    have h2 := Finset.sum_filter_add_sum_filter_not ((Finset.Icc N (2 * N)).filter (fun n => ¬ 5 * n < 6 * N))
      (fun n => 5 * n ≤ 9 * N) f
    have e2 : ((Finset.Icc N (2 * N)).filter (fun n => ¬ 5 * n < 6 * N)).filter (fun n => 5 * n ≤ 9 * N) =
        (Finset.Icc N (2 * N)).filter (fun n => 6 * N ≤ 5 * n ∧ 5 * n ≤ 9 * N) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    have e3 : ((Finset.Icc N (2 * N)).filter (fun n => ¬ 5 * n < 6 * N)).filter (fun n => ¬ 5 * n ≤ 9 * N) =
        (Finset.Icc N (2 * N)).filter (fun n => 9 * N < 5 * n) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [e2, e3] at h2
    rw [← h1, ← h2]; ring

lemma exists_fiber {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (ht : t.Nonempty)
    (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) :
    ∃ y ∈ t, s.card ≤ t.card * (s.filter fun a => f a = y).card := by
  by_contra h
  push Not at h
  have hsum : ∑ y ∈ t, (s.filter fun a => f a = y).card = s.card :=
    (Finset.card_eq_sum_card_fiberwise hf).symm
  have : ∑ y ∈ t, t.card * (s.filter fun a => f a = y).card < ∑ y ∈ t, s.card :=
    Finset.sum_lt_sum_of_nonempty ht (fun y hy => h y hy)
  rw [← Finset.mul_sum, hsum] at this
  simp at this

/-- Thin a 1-separated finite set to a `q`-separated subset, losing a factor `2q`. -/
lemma exists_thin (Q : Finset ℝ) (hQ : IsSeparated 1 Q) (q : ℕ) (hq : 1 ≤ q) :
    ∃ Q' ⊆ Q, IsSeparated (q : ℝ) Q' ∧ Q.card ≤ 2 * q * Q'.card := by
  classical
  by_cases hne : Q.Nonempty
  · have hq0 : (0:ℤ) < 2 * q := by omega
    obtain ⟨y, hy, hle⟩ := exists_fiber Q (Finset.Ico (0:ℤ) (2 * q)) (by
        refine ⟨0, ?_⟩; simp; omega)
      (fun t => ⌊t⌋ % (2 * q : ℤ)) (by
        intro t _
        simp only [Finset.mem_Ico]
        exact ⟨Int.emod_nonneg _ hq0.ne', Int.emod_lt_of_pos _ hq0⟩)
    refine ⟨Q.filter fun a => ⌊a⌋ % (2 * q : ℤ) = y, Finset.filter_subset _ _, ?_, ?_⟩
    · intro t ht t' ht' hne'
      simp only [Finset.mem_filter] at ht ht'
      have h1 : 1 ≤ |t - t'| := hQ t ht.1 t' ht'.1 hne'
      have hfl : ⌊t⌋ ≠ ⌊t'⌋ := by
        intro heq
        have a1 := Int.floor_le t
        have a2 := Int.lt_floor_add_one t
        have a3 := Int.floor_le t'
        have a4 := Int.lt_floor_add_one t'
        rw [heq] at a1 a2
        rcases abs_cases (t - t') with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      have hdvd : (2 * q : ℤ) ∣ ⌊t⌋ - ⌊t'⌋ := by
        apply Int.ModEq.dvd
        exact (ht'.2.trans ht.2.symm)
      have hne2 : ⌊t⌋ - ⌊t'⌋ ≠ 0 := sub_ne_zero.2 hfl
      have hge : (2 * q : ℤ) ≤ |⌊t⌋ - ⌊t'⌋| := Int.le_of_dvd (abs_pos.2 hne2) ((dvd_abs _ _).2 hdvd)
      have hge' : (2 * q : ℝ) ≤ |((⌊t⌋ - ⌊t'⌋ : ℤ) : ℝ)| := by
        have := (Int.cast_le (R := ℝ)).2 hge
        simpa using this
      have a1 := Int.floor_le t
      have a2 := Int.lt_floor_add_one t
      have a3 := Int.floor_le t'
      have a4 := Int.lt_floor_add_one t'
      push_cast at hge'
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      rcases abs_cases (t - t') with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases ((⌊t⌋ : ℝ) - ⌊t'⌋) with ⟨h', _⟩ | ⟨h', _⟩ <;> linarith
    · have : Q.card ≤ (Finset.Ico (0:ℤ) (2 * q)).card * (Q.filter fun a => ⌊a⌋ % (2 * q : ℤ) = y).card := hle
      have hc : (Finset.Ico (0:ℤ) (2 * q)).card = 2 * q := by simp; omega
      rwa [hc] at this
  · refine ⟨∅, Finset.empty_subset _, fun t ht => by simp at ht, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.1 hne]

lemma card_filter_pos_of_ne_zero (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    (Finset.univ.filter fun i => m i ≠ 0).card = 1 ∨
    (Finset.univ.filter fun i => m i ≠ 0).card = 2 ∨
    (Finset.univ.filter fun i => m i ≠ 0).card = 3 := by
  have h1 : 0 < (Finset.univ.filter fun i => m i ≠ 0).card := by
    apply Finset.card_pos.2
    by_contra h
    apply hm
    funext i
    by_contra hi
    exact h ⟨i, by simpa using hi⟩
  have h2 : (Finset.univ.filter fun i => m i ≠ 0).card ≤ 3 := by
    calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ _
      _ = 3 := by simp
  omega

lemma norm_tsum_ne_zero_le (f : (Fin 3 → ℤ) → ℂ) :
    ‖∑' m : {m : Fin 3 → ℤ // m ≠ 0}, f m‖ ≤
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 1}, f m‖ +
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 2}, f m‖ +
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 3}, f m‖ := by
  by_cases hs : Summable (fun m : {m : Fin 3 → ℤ // m ≠ 0} => f m)
  · set A : Set (Fin 3 → ℤ) := {m | m ≠ 0} with hA
    set B : ℕ → Set (Fin 3 → ℤ) := fun k => {m | (Finset.univ.filter fun i => m i ≠ 0).card = k} with hB
    have hsA : Summable (A.indicator f) := (summable_subtype_iff_indicator).1 hs
    have hBA : ∀ k, k ≠ 0 → B k ⊆ A := by
      intro k hk m hm
      simp only [hB, hA, Set.mem_ofPred_eq] at hm ⊢
      rintro rfl
      simp at hm
      exact hk hm.symm
    have hsB : ∀ k, k ≠ 0 → Summable ((B k).indicator f) := by
      intro k hk
      have h : (B k).indicator f = (B k).indicator (A.indicator f) := by
        funext m
        by_cases hm : m ∈ B k
        · simp [Set.indicator_of_mem hm, Set.indicator_of_mem (hBA k hk hm)]
        · simp [Set.indicator_of_notMem hm]
      rw [h]
      exact hsA.indicator _
    have hsum : A.indicator f = ∑ k ∈ ({1, 2, 3} : Finset ℕ), (B k).indicator f := by
      funext m
      simp only [Finset.sum_apply]
      by_cases hm : m ∈ A
      · rw [Set.indicator_of_mem hm]
        have hm' : m ≠ 0 := hm
        rcases card_filter_pos_of_ne_zero m hm' with h | h | h <;>
          simp [Set.indicator, hB, h]
      · have hm0 : m = 0 := by simpa [hA] using hm
        subst hm0
        simp [Set.indicator, hB]
        intro h
        exact absurd h hm
    have e1 : ∀ k, ∑' m : B k, f m = ∑' m, (B k).indicator f m := fun k => tsum_subtype (B k) f
    have e0 : ∑' m : A, f m = ∑' m, A.indicator f m := tsum_subtype A f
    show ‖∑' m : A, f m‖ ≤ ‖∑' m : B 1, f m‖ + ‖∑' m : B 2, f m‖ + ‖∑' m : B 3, f m‖
    rw [e0, e1, e1, e1, hsum]
    have := Summable.tsum_finsetSum (s := ({1, 2, 3} : Finset ℕ)) (f := fun k m => (B k).indicator f m)
      (fun k hk => hsB k (by simp at hk; omega))
    simp only [Finset.sum_apply]
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    simp [Finset.sum_insert, add_assoc]
  · rw [tsum_eq_zero_of_not_summable hs]
    simp only [norm_zero]
    positivity

/-! ### Generic algebra -/

lemma eq_of_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a = Real.log b) : a = b :=
  Real.log_injOn_pos ha hb h

/-- Self-bounding: if `X ≤ A + B (∑ c_j X^{p_j})^{1/3}` with `p_j < 3`, then
`X ≤ 2A + ∑ (8 J B³ c_j)^{1/(3-p_j)}`. -/
lemma selfbound {J : ℕ} {X A B : ℝ} (c p : Fin J → ℝ) (hX : 0 < X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ∀ j, 0 ≤ c j) (hp : ∀ j, p j < 3)
    (h : X ≤ A + B * (∑ j, c j * X ^ (p j)) ^ (1 / 3 : ℝ)) :
    X ≤ 2 * A + ∑ j, (8 * (J : ℝ) * B ^ 3 * c j) ^ (1 / (3 - p j)) := by
  have hT : ∀ j, 0 ≤ (8 * (J : ℝ) * B ^ 3 * c j) ^ (1 / (3 - p j)) := fun j =>
    Real.rpow_nonneg (by have := hc j; positivity) _
  have hsum0 : 0 ≤ ∑ j, (8 * (J : ℝ) * B ^ 3 * c j) ^ (1 / (3 - p j)) :=
    Finset.sum_nonneg (fun j _ => hT j)
  by_cases h2 : X ≤ 2 * A
  · linarith
  push Not at h2
  set S := ∑ j, c j * X ^ (p j) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (Real.rpow_nonneg hX.le _))
  set u := S ^ (1 / 3 : ℝ) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hS0 _
  have hu3 : u ^ 3 = S := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hS0]; norm_num
  have hBu : X < 2 * (B * u) := by linarith
  have hX3 : X ^ 3 < 8 * B ^ 3 * S := by
    calc X ^ 3 < (2 * (B * u)) ^ 3 := pow_lt_pow_left₀ hBu hX.le (by norm_num)
      _ = 8 * B ^ 3 * u ^ 3 := by ring
      _ = 8 * B ^ 3 * S := by rw [hu3]
  have hJ : 0 < J := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ
      have : S = 0 := by simp [hSdef]
      rw [this] at hX3
      nlinarith [pow_pos hX 3]
    · exact hJ
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hconst : ∑ _j : Fin J, X ^ 3 / J = X ^ 3 := by
    simp [Finset.sum_const]; field_simp
  have hlt : ∑ _j : Fin J, X ^ 3 / J < ∑ j, 8 * B ^ 3 * (c j * X ^ (p j)) := by
    rw [hconst, ← Finset.mul_sum]; exact hX3
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt hlt
  have hj' : X ^ 3 < 8 * (J : ℝ) * B ^ 3 * c j * X ^ (p j) := by
    rw [div_lt_iff₀ hJr] at hj
    calc X ^ 3 < _ := hj
      _ = _ := by ring
  have hXp : 0 < X ^ (p j) := Real.rpow_pos_of_pos hX _
  have h3p : 0 < 3 - p j := by linarith [hp j]
  have hXe : X ^ (3 - p j) < 8 * (J : ℝ) * B ^ 3 * c j := by
    rw [Real.rpow_sub hX, div_lt_iff₀ hXp]
    have : X ^ (3 : ℝ) = X ^ 3 := by rw [← Real.rpow_natCast]; norm_num
    rw [this]; exact hj'
  have hfin : X ≤ (8 * (J : ℝ) * B ^ 3 * c j) ^ (1 / (3 - p j)) := by
    have e : X = (X ^ (3 - p j)) ^ (1 / (3 - p j)) := by
      rw [← Real.rpow_mul hX.le, mul_one_div_cancel h3p.ne', Real.rpow_one]
    calc X = (X ^ (3 - p j)) ^ (1 / (3 - p j)) := e
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hX.le _) hXe.le (by positivity)
  have := Finset.single_le_sum (fun i _ => hT i) (Finset.mem_univ j)
  linarith

/-- The constant produced by `conv`. -/
noncomputable def convK (κ e γ α β d : ℝ) : ℝ :=
  κ ^ e * 2 ^ d * 2 ^ (γ * e) * 2 ^ (α * e) * 4 ^ (β * e)

lemma convK_nonneg {κ e γ α β d : ℝ} (hκ : 0 ≤ κ) : 0 ≤ convK κ e γ α β d := by
  unfold convK; positivity

/-- Converting a bound at scale `M` with `M^s = N^σ / 4` and `T' = 2T` into one at scale `N`. -/
lemma conv {κ e γ α β d δ' T N M σ s : ℝ} (hκ : 0 < κ) (he : 0 < e) (he1 : e ≤ 1) (hα : 0 ≤ α)
    (hd : 0 ≤ d) (hdδ : d ≤ δ') (hT : 1 ≤ T) (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ 2 * N)
    (hs : M ^ s = N ^ σ / 4) :
    (κ * (2 * T) ^ d * (2 * T) ^ γ * M ^ (α - β * s)) ^ e ≤
      convK κ e γ α β δ' * T ^ δ' * (T ^ (γ * e) * N ^ ((α - β * σ) * e)) := by
  have hT0 : 0 < T := by linarith
  have h1 : M ^ (α - β * s) = M ^ α * (N ^ σ / 4) ^ (-β) := by
    rw [← hs, ← Real.rpow_mul hM.le, ← Real.rpow_add hM]; congr 1; ring
  have hL : (κ * (2 * T) ^ d * (2 * T) ^ γ * M ^ (α - β * s)) ^ e =
      κ ^ e * (2 * T) ^ (d * e) * 2 ^ (γ * e) * T ^ (γ * e) * M ^ (α * e) * 4 ^ (β * e) *
        N ^ (-(σ * β * e)) := by
    rw [h1]
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div]
    ring
  have hR : convK κ e γ α β δ' * T ^ δ' * (T ^ (γ * e) * N ^ ((α - β * σ) * e)) =
      κ ^ e * (2 ^ δ' * T ^ δ') * 2 ^ (γ * e) * T ^ (γ * e) * (2 ^ (α * e) * N ^ (α * e)) *
        4 ^ (β * e) * N ^ (-(σ * β * e)) := by
    unfold convK
    have : N ^ ((α - β * σ) * e) = N ^ (α * e) * N ^ (-(σ * β * e)) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    rw [this]; ring
  rw [hL, hR]
  have hA : (2 * T) ^ (d * e) ≤ 2 ^ δ' * T ^ δ' := by
    rw [← Real.mul_rpow (by norm_num) hT0.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    nlinarith
  have hB : M ^ (α * e) ≤ 2 ^ (α * e) * N ^ (α * e) := by
    rw [← Real.mul_rpow (by norm_num) hN.le]
    exact Real.rpow_le_rpow hM.le hMN (by positivity)
  gcongr

/-! ### The bound on `‖S₁‖ + ‖S₂‖ + ‖S₃‖` and the target -/

/-- The bound on `‖S₁‖ + ‖S₂‖ + ‖S₃‖` assembled from Props 5.1, 6.1 (parameter `k`), 11.2. -/
noncomputable def Sm (k : ℕ) (C1 C2 C3 δ T M X s : ℝ) : ℝ :=
  C1 * T ^ (-10 : ℝ) +
  C2 * T ^ δ * (M ^ 2 * X ^ 2 + T * M * X ^ (2 - 1 / (k : ℝ)) +
    M ^ 2 * X ^ 2 * (T ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) +
  C3 * T ^ δ * (T ^ 2 * X ^ (3 / 2 : ℝ) + T * X * M ^ (3 - 2 * s) +
    T * X ^ 2 * M ^ (3 / 2 - s) + T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * M ^ (3 / 2 - s))

/-- The eight-term right-hand side of (12.1). -/
noncomputable def tgt (k : ℕ) (T N σ : ℝ) : ℝ :=
  N ^ (2 - 2 * σ) + N ^ (5 - 6 * σ) +
    T ^ ((k : ℝ) / (k + 1)) * N ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
    N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
    T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
    T * N ^ (9 / 2 - 7 * σ) + T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19)

lemma tgt_nonneg (k : ℕ) {T N σ : ℝ} (hT : 0 < T) (hN : 0 < N) : 0 ≤ tgt k T N σ := by
  unfold tgt; positivity

lemma tgt_ge (k : ℕ) {T N σ : ℝ} (hT : 0 < T) (hN : 0 < N) :
    N ^ (2 - 2 * σ) ≤ tgt k T N σ ∧ N ^ (5 - 6 * σ) ≤ tgt k T N σ ∧
    T ^ ((k : ℝ) / (k + 1)) * N ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) ≤ tgt k T N σ ∧
    N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) ≤ tgt k T N σ ∧
    T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) ≤ tgt k T N σ ∧
    T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) ≤ tgt k T N σ ∧
    T * N ^ (9 / 2 - 7 * σ) ≤ tgt k T N σ ∧
    T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19) ≤ tgt k T N σ := by
  unfold tgt
  have a0 : 0 ≤ N ^ (2 - 2 * σ) := by positivity
  have a1 : 0 ≤ N ^ (5 - 6 * σ) := by positivity
  have a2 : 0 ≤ T ^ ((k : ℝ) / (k + 1)) * N ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) := by positivity
  have a3 : 0 ≤ N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) := by
    positivity
  have a4 : 0 ≤ T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  have a5 : 0 ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have a6 : 0 ≤ T * N ^ (9 / 2 - 7 * σ) := by positivity
  have a7 : 0 ≤ T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### The self-bounding algebra -/

lemma inv_one_add_pos_le {x : ℝ} (hx : 0 ≤ x) : 0 < 1 / (1 + x) ∧ 1 / (1 + x) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; linarith

lemma term_le {Y κ e γ α β δ' T N M σ s G : ℝ}
    (hY : Y = κ * (2 * T) ^ δ' * (2 * T) ^ γ * M ^ (α - β * s)) (hκ : 0 < κ) (he : 0 < e)
    (he1 : e ≤ 1) (hα : 0 ≤ α) (hδ : 0 ≤ δ') (hT : 1 ≤ T) (hN : 0 < N) (hM : 0 < M)
    (hMN : M ≤ 2 * N) (hs : M ^ s = N ^ σ / 4) (hG : T ^ (γ * e) * N ^ ((α - β * σ) * e) ≤ G) :
    Y ^ e ≤ convK κ e γ α β δ' * T ^ δ' * G := by
  rw [hY]
  refine (conv hκ he he1 hα hδ le_rfl hT hN hM hMN hs).trans ?_
  have hT0 : 0 < T := by linarith
  exact mul_le_mul_of_nonneg_left hG (mul_nonneg (convK_nonneg hκ.le) (by positivity))

set_option maxHeartbeats 4000000 in
lemma alg (k : ℕ) (hk : 1 ≤ k) {C1 C2 C3 C4 δ' : ℝ} (h1 : 0 < C1) (h2 : 0 < C2) (h3 : 0 < C3)
    (h4 : 0 < C4) (hδ : 0 < δ') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T N M σ s X : ℝ, 1 ≤ T → 1 ≤ N → 0 < M → M ≤ 2 * N →
      M ^ s = N ^ σ / 4 → 0 ≤ X →
      X ≤ C4 * (M ^ (2 - 2 * s) + M ^ (1 - 2 * s) * (Sm k C1 C2 C3 δ' (2 * T) M X s) ^ (1 / 3 : ℝ)) →
      X ≤ K * T ^ δ' * tgt k T N σ := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hκ1 : 0 < 8 * 8 * C4 ^ 3 * C1 := by positivity
  have hκ2 : 0 < 8 * 8 * C4 ^ 3 * C2 := by positivity
  have hκ3 : 0 < 8 * 8 * C4 ^ 3 * C3 := by positivity
  refine ⟨convK (2 * C4) 1 0 2 2 δ' +
    (convK (8 * 8 * C4 ^ 3 * C1) (1 / (3 - 0)) (-10) 3 6 δ' +
     convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - 2)) 0 5 6 δ' +
     convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 1 / (k : ℝ)))) 1 4 6 δ' +
     convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 3 / (4 * (k : ℝ))))) (1 / (2 * (k : ℝ))) 5 6 δ' +
     convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 3 / 2)) 2 3 6 δ' +
     convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 1)) 1 6 8 δ' +
     convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 2)) 1 (9 / 2) 7 δ' +
     convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 29 / 16)) (9 / 8) (9 / 2) 7 δ'), ?_, ?_⟩
  · unfold convK; positivity
  intro T N M σ s X hT hN hM hMN hs hX0 hX
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have htg := tgt_ge k (σ := σ) hT0 hN0
  have htg0 := tgt_nonneg k (σ := σ) hT0 hN0
  rcases hX0.eq_or_lt with hX0' | hXp
  · rw [← hX0']
    have : 0 ≤ convK (2 * C4) 1 0 2 2 δ' +
      (convK (8 * 8 * C4 ^ 3 * C1) (1 / (3 - 0)) (-10) 3 6 δ' +
       convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - 2)) 0 5 6 δ' +
       convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 1 / (k : ℝ)))) 1 4 6 δ' +
       convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 3 / (4 * (k : ℝ))))) (1 / (2 * (k : ℝ))) 5 6 δ' +
       convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 3 / 2)) 2 3 6 δ' +
       convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 1)) 1 6 8 δ' +
       convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 2)) 1 (9 / 2) 7 δ' +
       convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 29 / 16)) (9 / 8) (9 / 2) 7 δ') := by
      unfold convK; positivity
    positivity
  set c : Fin 8 → ℝ := ![C1 * (2 * T) ^ δ' * (2 * T) ^ (-10 : ℝ),
    C2 * (2 * T) ^ δ' * M ^ (2 : ℝ),
    C2 * (2 * T) ^ δ' * (2 * T) * M,
    C2 * (2 * T) ^ δ' * (2 * T) ^ (1 / (2 * (k : ℝ))) * M ^ (2 : ℝ),
    C3 * (2 * T) ^ δ' * (2 * T) ^ (2 : ℝ),
    C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 - 2 * s),
    C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 / 2 - s),
    C3 * (2 * T) ^ δ' * (2 * T) ^ (9 / 8 : ℝ) * M ^ (3 / 2 - s)] with hc
  set p : Fin 8 → ℝ := ![0, 2, 2 - 1 / (k : ℝ), 2 - 3 / (4 * (k : ℝ)), 3 / 2, 1, 2, 29 / 16] with hp
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j; fin_cases j <;> simp [hc] <;> positivity
  have hp3 : ∀ j, p j < 3 := by
    have : 0 < 1 / (k : ℝ) := by positivity
    have : 0 < (k : ℝ)⁻¹ := by positivity
    have : 0 < 3 / (4 * (k : ℝ)) := by positivity
    intro j; fin_cases j <;> simp [hp] <;> linarith
  have hS : Sm k C1 C2 C3 δ' (2 * T) M X s ≤ ∑ j, c j * X ^ (p j) := by
    simp only [Fin.sum_univ_eight, hc, hp, Matrix.cons_val]
    have q0 : C1 * (2 * T) ^ (-10 : ℝ) ≤ C1 * (2 * T) ^ δ' * (2 * T) ^ (-10 : ℝ) * X ^ (0 : ℝ) := by
      have : 1 ≤ (2 * T) ^ δ' := Real.one_le_rpow (by linarith) hδ.le
      rw [Real.rpow_zero, mul_one]
      calc C1 * (2 * T) ^ (-10 : ℝ) = C1 * 1 * (2 * T) ^ (-10 : ℝ) := by ring
        _ ≤ _ := by gcongr
    have q1 : C2 * (2 * T) ^ δ' * (M ^ 2 * X ^ 2) = C2 * (2 * T) ^ δ' * M ^ (2 : ℝ) * X ^ (2 : ℝ) := by
      simp only [Real.rpow_two]; ring
    have q2 : C2 * (2 * T) ^ δ' * (2 * T * M * X ^ (2 - 1 / (k : ℝ))) =
        C2 * (2 * T) ^ δ' * (2 * T) * M * X ^ (2 - 1 / (k : ℝ)) := by ring
    have q3 : C2 * (2 * T) ^ δ' * (M ^ 2 * X ^ 2 * ((2 * T) ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) =
        C2 * (2 * T) ^ δ' * (2 * T) ^ (1 / (2 * (k : ℝ))) * M ^ (2 : ℝ) * X ^ (2 - 3 / (4 * (k : ℝ))) := by
      apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
      push_cast
      field_simp
      ring
    have q4 : C3 * (2 * T) ^ δ' * ((2 * T) ^ 2 * X ^ (3 / 2 : ℝ)) =
        C3 * (2 * T) ^ δ' * (2 * T) ^ (2 : ℝ) * X ^ (3 / 2 : ℝ) := by
      simp only [Real.rpow_two]; ring
    have q5 : C3 * (2 * T) ^ δ' * (2 * T * X * M ^ (3 - 2 * s)) =
        C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 - 2 * s) * X ^ (1 : ℝ) := by
      simp only [Real.rpow_one]; ring
    have q6 : C3 * (2 * T) ^ δ' * (2 * T * X ^ 2 * M ^ (3 / 2 - s)) =
        C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 / 2 - s) * X ^ (2 : ℝ) := by
      simp only [Real.rpow_two]; ring
    have q7 : C3 * (2 * T) ^ δ' * ((2 * T) ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * M ^ (3 / 2 - s)) =
        C3 * (2 * T) ^ δ' * (2 * T) ^ (9 / 8 : ℝ) * M ^ (3 / 2 - s) * X ^ (29 / 16 : ℝ) := by ring
    have hSm : Sm k C1 C2 C3 δ' (2 * T) M X s = C1 * (2 * T) ^ (-10 : ℝ) +
        C2 * (2 * T) ^ δ' * (M ^ 2 * X ^ 2) +
        C2 * (2 * T) ^ δ' * (2 * T * M * X ^ (2 - 1 / (k : ℝ))) +
        C2 * (2 * T) ^ δ' * (M ^ 2 * X ^ 2 * ((2 * T) ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) +
        C3 * (2 * T) ^ δ' * ((2 * T) ^ 2 * X ^ (3 / 2 : ℝ)) +
        C3 * (2 * T) ^ δ' * (2 * T * X * M ^ (3 - 2 * s)) +
        C3 * (2 * T) ^ δ' * (2 * T * X ^ 2 * M ^ (3 / 2 - s)) +
        C3 * (2 * T) ^ δ' * ((2 * T) ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * M ^ (3 / 2 - s)) := by
      unfold Sm; ring
    rw [hSm, q1, q2, q3, q4, q5, q6, q7]
    linarith
  have hSm0 : 0 ≤ Sm k C1 C2 C3 δ' (2 * T) M X s := by unfold Sm; positivity
  have hsb := selfbound c p hXp (A := C4 * M ^ (2 - 2 * s)) (B := C4 * M ^ (1 - 2 * s))
    (by positivity) (by positivity) hc0 hp3 (hX.trans (by
      rw [mul_add, ← mul_assoc]
      gcongr))
  simp only [Fin.sum_univ_eight, hc, hp, Matrix.cons_val] at hsb
  -- the A-term
  have bA : 2 * (C4 * M ^ (2 - 2 * s)) ≤ convK (2 * C4) 1 0 2 2 δ' * T ^ δ' * tgt k T N σ := by
    have h := conv (κ := 2 * C4) (e := 1) (γ := 0) (α := 2) (β := 2) (d := 0) (δ' := δ')
      (by positivity) one_pos le_rfl (by norm_num) le_rfl hδ.le hT hN0 hM hMN hs
    simp only [Real.rpow_zero, Real.rpow_one, mul_one, one_mul] at h
    calc 2 * (C4 * M ^ (2 - 2 * s)) = 2 * C4 * M ^ (2 - 2 * s) := by ring
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_left htg.1 (mul_nonneg (convK_nonneg (by positivity))
          (by positivity))
  have b0 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 * (C1 * (2 * T) ^ δ' * (2 * T) ^ (-10 : ℝ))) ^
      (1 / (3 - 0 : ℝ)) ≤ convK (8 * 8 * C4 ^ 3 * C1) (1 / (3 - 0)) (-10) 3 6 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ1 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have e1 : T ^ (-10 * (1 / (3 - 0)) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
      have e2 : N ^ ((3 - 6 * σ) * (1 / (3 - 0))) ≤ N ^ (2 - 2 * σ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      calc _ ≤ 1 * N ^ (2 - 2 * σ) := mul_le_mul e1 e2 (by positivity) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact htg.1
  have b1 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 * (C2 * (2 * T) ^ δ' * M ^ (2 : ℝ))) ^
      (1 / (3 - 2 : ℝ)) ≤ convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - 2)) 0 5 6 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ2 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have : (5 - 6 * σ) * (1 / (3 - 2)) = 5 - 6 * σ := by ring
      rw [this, zero_mul, Real.rpow_zero, one_mul]; exact htg.2.1
  have ek2' : (3 : ℝ) - (2 - 1 / (k : ℝ)) = 1 + 1 / k := by ring
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk3 : 4 * (k : ℝ) + 3 ≠ 0 := by positivity
  have ek2 : (1 : ℝ) / (3 - (2 - 1 / (k : ℝ))) = k / (k + 1) := by
    rw [ek2', div_eq_div_iff (by positivity) hk1]; field_simp
  have b2 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 * (C2 * (2 * T) ^ δ' * (2 * T) * M)) ^
      (1 / (3 - (2 - 1 / (k : ℝ)))) ≤
      convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 1 / (k : ℝ)))) 1 4 6 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ2 ?_ ?_ (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · rw [ek2']; exact (inv_one_add_pos_le (by positivity)).1
    · rw [ek2']; exact (inv_one_add_pos_le (by positivity)).2
    · rw [ek2, one_mul]; exact htg.2.2.1
  have ek3' : (3 : ℝ) - (2 - 3 / (4 * (k : ℝ))) = 1 + 3 / (4 * k) := by ring
  have ek3 : (1 : ℝ) / (3 - (2 - 3 / (4 * (k : ℝ)))) = 4 * k / (4 * k + 3) := by
    rw [ek3', div_eq_div_iff (by positivity) hk3]; field_simp
  have ek3'' : 1 / (2 * (k : ℝ)) * (4 * k / (4 * k + 3)) = 2 / (4 * k + 3) := by field_simp; ring
  have b3 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 *
      (C2 * (2 * T) ^ δ' * (2 * T) ^ (1 / (2 * (k : ℝ))) * M ^ (2 : ℝ))) ^
      (1 / (3 - (2 - 3 / (4 * (k : ℝ))))) ≤
      convK (8 * 8 * C4 ^ 3 * C2) (1 / (3 - (2 - 3 / (4 * (k : ℝ))))) (1 / (2 * (k : ℝ))) 5 6 δ' *
        T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ2 ?_ ?_ (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · rw [ek3']; exact (inv_one_add_pos_le (by positivity)).1
    · rw [ek3']; exact (inv_one_add_pos_le (by positivity)).2
    · rw [ek3, ek3'', mul_comm]; exact htg.2.2.2.1
  have b4 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 * (C3 * (2 * T) ^ δ' * (2 * T) ^ (2 : ℝ))) ^
      (1 / (3 - 3 / 2 : ℝ)) ≤ convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 3 / 2)) 2 3 6 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ3 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have e1 : (2 : ℝ) * (1 / (3 - 3 / 2)) = 4 / 3 := by norm_num
      have e2 : (3 - 6 * σ) * (1 / (3 - 3 / 2)) = 2 - 4 * σ := by ring
      rw [e1, e2]; exact htg.2.2.2.2.1
  have b5 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 *
      (C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 - 2 * s))) ^
      (1 / (3 - 1 : ℝ)) ≤ convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 1)) 1 6 8 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ3 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have e1 : (1 : ℝ) * (1 / (3 - 1)) = 1 / 2 := by norm_num
      have e2 : (6 - 8 * σ) * (1 / (3 - 1)) = 3 - 4 * σ := by ring
      rw [e1, e2]; exact htg.2.2.2.2.2.1
  have b6 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 *
      (C3 * (2 * T) ^ δ' * (2 * T) * M ^ (3 / 2 - s))) ^
      (1 / (3 - 2 : ℝ)) ≤ convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 2)) 1 (9 / 2) 7 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ3 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have e1 : (1 : ℝ) * (1 / (3 - 2)) = 1 := by norm_num
      have e2 : (9 / 2 - 7 * σ) * (1 / (3 - 2)) = 9 / 2 - 7 * σ := by ring
      rw [e1, e2, Real.rpow_one]; exact htg.2.2.2.2.2.2.1
  have b7 : (8 * ((8 : ℕ) : ℝ) * (C4 * M ^ (1 - 2 * s)) ^ 3 *
      (C3 * (2 * T) ^ δ' * (2 * T) ^ (9 / 8 : ℝ) * M ^ (3 / 2 - s))) ^
      (1 / (3 - 29 / 16 : ℝ)) ≤
      convK (8 * 8 * C4 ^ 3 * C3) (1 / (3 - 29 / 16)) (9 / 8) (9 / 2) 7 δ' * T ^ δ' * tgt k T N σ := by
    refine term_le ?_ hκ3 (by norm_num) (by norm_num) (by norm_num) hδ.le hT hN0 hM hMN hs ?_
    · apply eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
      ring
    · have e1 : (9 / 8 : ℝ) * (1 / (3 - 29 / 16)) = 18 / 19 := by norm_num
      have e2 : (9 / 2 - 7 * σ) * (1 / (3 - 29 / 16)) = 72 / 19 - 112 * σ / 19 := by ring
      rw [e1, e2]; exact htg.2.2.2.2.2.2.2
  refine hsb.trans ?_
  refine (add_le_add bA (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add b0 b1) b2) b3) b4) b5) b6) b7)).trans (le_of_eq ?_)
  ring


/-! ### One piece: combining Props 4.6, 5.1, 6.1, 11.2 -/

lemma analytic (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k)
    (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C1 C2 C3 C4 T₁ : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ 0 < C4 ∧
      ∀ T : ℝ, T₁ ≤ T → ∀ M : ℕ, (M : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → 1 < (M : ℝ) →
      ∀ s : ℝ, ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc 0 (0 + T)) → (∀ t ∈ W, (M : ℝ) ^ s < ‖smoothedPoly w M b t‖) →
      (W.card : ℝ) ≤ C4 * ((M : ℝ) ^ (2 - 2 * s) + (M : ℝ) ^ (1 - 2 * s) *
        (Sm k C1 C2 C3 δ' T M W.card s) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C4, hC4⟩ := card_le_of_large_smoothedPoly_Iterm_pos w hw ε hε
  obtain ⟨C1, hC1⟩ := norm_S_one_le w hw ε hε
  obtain ⟨C2, T2, hC2⟩ := norm_S_two_le w hw ε hε k hk δ' hδ'
  obtain ⟨C3, T3, hC3⟩ := norm_S_three_le w hw ε hε δ' hδ'
  refine ⟨max C1 1, max C2 1, max C3 1, max |C4| 1, max T2 T3, by positivity, by positivity,
    by positivity, by positivity, ?_⟩
  intro T hT N hmem hN1 σ' b hb W hsep hwin hD1
  have hN0 : 0 < (N : ℝ) := by linarith
  have hTp : 0 < T := by linarith [hmem.2]
  have hT2 : T2 ≤ T := le_trans (le_max_left _ _) hT
  have hT3 : T3 ≤ T := le_trans (le_max_right _ _) hT
  set Nr : ℝ := (N : ℝ) with hNr_def
  have hD2 : ∀ t ∈ W, Nr ^ σ' ≤ ‖smoothedPoly w N b t‖ := fun t ht => (hD1 t ht).le
  have h46 := hC4 T N hmem σ' b hb W 0 hsep hwin hD1
  have h51 := hC1 T N hmem W 0 hsep hwin
  have h61 := hC2 T hT2 N hmem W 0 hsep hwin
  have h111 := hC3 T hT3 N hmem σ' b hb W 0 hsep hwin hD2
  have hE2 : 0 ≤ (Nr ^ 2 * (W.card : ℝ) ^ 2 + T * Nr * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
      Nr ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
    positivity
  have hE3 : 0 ≤ (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) + T * (W.card : ℝ) * Nr ^ (3 - 2 * σ') +
      T * (W.card : ℝ) ^ 2 * Nr ^ (3 / 2 - σ') +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * Nr ^ (3 / 2 - σ')) := by
    positivity
  have m1 : ‖S 1 w N W‖ ≤ max C1 1 * T ^ (-10 : ℝ) :=
    h51.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hTp.le _))
  have m2 : ‖S 2 w N W‖ ≤ max C2 1 * T ^ δ' * (Nr ^ 2 * (W.card : ℝ) ^ 2 +
      T * Nr * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
      Nr ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) :=
    h61.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hTp.le _)) hE2)
  have m3 : ‖S 3 w N W‖ ≤ max C3 1 * T ^ δ' * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * (W.card : ℝ) * Nr ^ (3 - 2 * σ') +
      T * (W.card : ℝ) ^ 2 * Nr ^ (3 / 2 - σ') +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * Nr ^ (3 / 2 - σ')) :=
    h111.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hTp.le _)) hE3)
  have hnorm : ‖∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m‖ ≤
      Sm k (max C1 1) (max C2 1) (max C3 1) δ' T Nr (W.card : ℝ) σ' := by
    refine (norm_tsum_ne_zero_le (Iterm w N W)).trans ?_
    unfold Sm
    have e1 : S 1 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 1},
      Iterm w N W m := rfl
    have e2 : S 2 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 2},
      Iterm w N W m := rfl
    have e3 : S 3 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 3},
      Iterm w N W m := rfl
    rw [← e1, ← e2, ← e3]
    linarith
  simp only at h46
  set Sm' := Sm k (max C1 1) (max C2 1) (max C3 1) δ' T Nr (W.card : ℝ) σ' with hSm'
  have hSm0 : 0 ≤ Sm' := (norm_nonneg _).trans hnorm
  set s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re with hs
  have hsle : |s| ≤ Sm' := (Complex.abs_re_le_norm _).trans hnorm
  have hc : |max s 0 ^ (1 / 3 : ℝ)| ≤ Sm' ^ (1 / 3 : ℝ) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le ((le_abs_self s).trans hsle) hSm0)
      (by norm_num)
  have hQ : 0 ≤ Nr ^ (1 - 2 * σ') := Real.rpow_nonneg hN0.le _
  have hP : 0 ≤ Nr ^ (2 - 2 * σ') := Real.rpow_nonneg hN0.le _
  have hpos : 0 ≤ Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * Sm' ^ (1 / 3 : ℝ) := by positivity
  calc (W.card : ℝ) ≤ C4 * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * max s 0 ^ (1 / 3 : ℝ)) := h46
    _ ≤ |C4 * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * max s 0 ^ (1 / 3 : ℝ))| := le_abs_self _
    _ = |C4| * |Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * max s 0 ^ (1 / 3 : ℝ)| := abs_mul _ _
    _ ≤ |C4| * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * Sm' ^ (1 / 3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hP, abs_mul, abs_of_nonneg hQ]
      have := mul_le_mul_of_nonneg_left hc hQ
      linarith
    _ ≤ max |C4| 1 * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * Sm' ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpos

/-! ### Proposition 12.1, the eight-term bound -/

theorem twelve_one (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (5 - 6 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
        T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T * (N : ℝ) ^ (9 / 2 - 7 * σ) + T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19)) := by
  intro δ hδ
  obtain ⟨w, hw⟩ := exists_weight
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨C1, C2, C3, C4, T₁, h1, h2, h3, h4, hA⟩ := analytic w hw (δ / 2) hδ2 k hk (δ / 2) hδ2
  obtain ⟨K, hK0, hK⟩ := alg k hk h1 h2 h3 h4 hδ2
  have ev1 : ∀ᶠ T : ℝ in Filter.atTop, T₁ ≤ T := Filter.eventually_ge_atTop _
  have ev2 : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T := Filter.eventually_ge_atTop _
  have ev3 : ∀ᶠ T : ℝ in Filter.atTop, 4 ≤ T ^ (1 / 12 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).eventually_ge_atTop _
  have ev4 : ∀ᶠ T : ℝ in Filter.atTop, 6 ≤ T ^ (5 / 6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6)).eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨12 * 2 ^ (δ / 2) * K, T₀, ?_⟩
  intro T hT N hN σ b hb R t hsep htT hV
  obtain ⟨hT1, hT1', hT4, hT6⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith
  have hN6r : (6 : ℝ) ≤ N := hT6.trans hN.1
  have hN6 : 6 ≤ N := by exact_mod_cast hN6r
  have hN0 : (0 : ℝ) < N := by linarith
  have htg0 : 0 ≤ tgt k T N σ := tgt_nonneg k hT0 hN0
  show (R : ℝ) ≤ 12 * 2 ^ (δ / 2) * K * T ^ δ * tgt k T N σ
  by_cases hR : R = 0
  · subst hR; simp only [Nat.cast_zero]; positivity
  set b' : ℕ → ℂ := fun n => if n = N then 0 else b n with hb'def
  have hb' : ∀ n, ‖b' n‖ ≤ 1 := by
    intro n; simp only [hb'def]; split_ifs <;> simp [hb n]
  have hsumeq : ∀ x : ℝ, ∑ n ∈ Finset.Icc N (2 * N), b' n * (n : ℂ) ^ ((x : ℂ) * I) =
      ∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((x : ℂ) * I) := by
    intro x
    have : Finset.Icc N (2 * N) = insert N (Finset.Ioc N (2 * N)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [this, Finset.sum_insert (by simp)]
    simp only [hb'def, if_pos rfl, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    have : n ≠ N := by simp only [Finset.mem_Ioc] at hn; omega
    simp [this]
  obtain ⟨M, A, hMA, hsum⟩ := pieces N hN6
  have hσpos : 0 < (N : ℝ) ^ σ := by positivity
  have hex : ∀ r, ∃ i : Fin 3,
      (N : ℝ) ^ σ / 3 ≤ ‖∑ n ∈ A i, b' n * (n : ℂ) ^ ((t r : ℂ) * I)‖ := by
    intro r
    by_contra hcon
    push Not at hcon
    have h := hV r
    rw [← hsumeq, hsum (fun n => b' n * (n : ℂ) ^ ((t r : ℂ) * I))] at h
    have h2 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun i => ∑ n ∈ A i, b' n * (n : ℂ) ^ ((t r : ℂ) * I))
    simp only [Fin.sum_univ_three] at h h2
    have := hcon 0; have := hcon 1; have := hcon 2
    linarith
  choose g hg using hex
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  obtain ⟨i, -, hfib⟩ := exists_fiber (Finset.univ : Finset (Fin R)) (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ _⟩ g (fun _ _ => Finset.mem_univ _)
  set S := (Finset.univ : Finset (Fin R)).filter (fun r => g r = i) with hS
  have hRS : R ≤ 3 * S.card := by simpa using hfib
  set P := S.image t with hP
  have hinj : Set.InjOn t S := by
    intro r _ s _ hrs
    by_contra hne
    have := hsep r s hne
    rw [hrs] at this; simp at this; linarith
  have hPcard : P.card = S.card := Finset.card_image_of_injOn hinj
  have hPsep : IsSeparated 1 P := by
    intro x hx y hy hxy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
    exact hsep r s (fun h => hxy (by rw [h]))
  have hPT : ∀ x ∈ P, x ∈ Set.Icc 0 T := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    exact htT r
  obtain ⟨hMpos, hM2N, hMN, hAi⟩ := hMA i
  set q : ℕ := ⌈(2 * T) ^ (δ / 2)⌉₊ with hq
  have hq1' : 1 ≤ (2 * T) ^ (δ / 2) := Real.one_le_rpow (by linarith) hδ2.le
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by
    rw [hq]; exact (Nat.ceil_pos.2 (by linarith)).ne')
  obtain ⟨Q', hQ'sub, hQ'sep, hcard⟩ := exists_thin P hPsep q hq1
  have hsep' : IsSeparated ((2 * T) ^ (δ / 2)) Q' := by
    intro x hx y hy hne
    exact le_trans (Nat.le_ceil _) (hQ'sep x hx y hy hne)
  have hwin : ∀ x ∈ Q', x ∈ Set.Icc 0 (0 + 2 * T) := by
    intro x hx
    have := hPT x (hQ'sub hx)
    exact ⟨this.1, by linarith [this.2]⟩
  have hMr : (M i : ℝ) ≤ 2 * N := by exact_mod_cast hMN
  have hNM : (N : ℝ) ≤ 2 * M i := by exact_mod_cast hM2N
  have hM1 : (1 : ℝ) < M i := by
    have : 3 ≤ M i := by omega
    exact_mod_cast (by omega : 1 < M i)
  have hmem : (M i : ℝ) ∈ Set.Icc ((2 * T) ^ (3 / 4 : ℝ)) (2 * T) := by
    refine ⟨?_, by linarith [hN.2]⟩
    have e1 : (2 * T) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hT0.le
    have e2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have e3 : T ^ (5 / 6 : ℝ) = T ^ (3 / 4 : ℝ) * T ^ (1 / 12 : ℝ) := by
      rw [← Real.rpow_add hT0]; norm_num
    have ha : 0 ≤ T ^ (3 / 4 : ℝ) := by positivity
    have := hN.1
    rw [e1]
    nlinarith [mul_nonneg ha (sub_nonneg.2 hT4), mul_nonneg ha (sub_nonneg.2 e2)]
  set s := Real.logb (M i) ((N : ℝ) ^ σ / 4) with hsdef
  have hs : (M i : ℝ) ^ s = (N : ℝ) ^ σ / 4 :=
    Real.rpow_logb (by linarith) hM1.ne' (by positivity)
  set b'' : ℕ → ℂ := fun n => if n ∈ A i then b' n else 0 with hb''def
  have hb'' : ∀ n, ‖b'' n‖ ≤ 1 := by
    intro n; simp only [hb''def]; split_ifs <;> simp [hb' n]
  have hD : ∀ x ∈ Q', (M i : ℝ) ^ s < ‖smoothedPoly w (M i) b'' x‖ := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 (hQ'sub hx)
    rw [hb''def, smoothed_eq w hw (M i) hMpos (A i) hAi b', hs]
    have := hg r
    have hgr : g r = i := (Finset.mem_filter.1 hr).2
    rw [hgr] at this
    linarith
  have hXb := hA (2 * T) (by linarith) (M i) hmem hM1 s b'' hb'' Q' hsep' hwin hD
  have hfin := hK T N (M i) σ s (Q'.card) hT1' (by linarith) (by linarith) hMr hs
    (Nat.cast_nonneg _) hXb
  have hRR : (R : ℝ) ≤ 3 * P.card := by rw [hPcard]; exact_mod_cast hRS
  have hPQ : (P.card : ℝ) ≤ 2 * q * Q'.card := by exact_mod_cast hcard
  have hq' : (q : ℝ) ≤ 2 * 2 ^ (δ / 2) * T ^ (δ / 2) := by
    have e1 : (q : ℝ) < (2 * T) ^ (δ / 2) + 1 := Nat.ceil_lt_add_one (by positivity)
    have e3 : (2 * T) ^ (δ / 2) = 2 ^ (δ / 2) * T ^ (δ / 2) := Real.mul_rpow (by norm_num) hT0.le
    linarith
  have hTT : T ^ δ = T ^ (δ / 2) * T ^ (δ / 2) := by rw [← Real.rpow_add hT0]; ring_nf
  calc (R : ℝ) ≤ 3 * (2 * q * Q'.card) := by linarith
    _ ≤ 3 * (2 * (2 * 2 ^ (δ / 2) * T ^ (δ / 2)) * (K * T ^ (δ / 2) * tgt k T N σ)) := by
      gcongr
    _ = 12 * 2 ^ (δ / 2) * K * T ^ δ * tgt k T N σ := by rw [hTT]; ring

end GuthMaynardS1213.P121.PartA

open GuthMaynard in
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (5 - 6 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
        T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T * (N : ℝ) ^ (9 / 2 - 7 * σ) + T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19)) :=
  GuthMaynardS1213.P121.PartA.twelve_one k hk
