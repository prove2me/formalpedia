-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:18:50.544121+00:00
-- url     : https://prove2.me/submissions/dcc973a5-ab83-49de-a7d2-ebbef3540fdc

import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly
import Theorems.Thm_GuthMaynard_card_le_of_large_values_classical
import Mathlib

section
section
namespace GuthMaynardGoal

open GuthMaynard Complex

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

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

open GuthMaynard

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

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

open GuthMaynard

theorem piece (w : ℝ → ℝ) (hw : IsWeight w) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ σ : ℝ, σ ∈ Set.Icc (7 / 10 : ℝ) (8 / 10) →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∀ T : ℝ, 0 ≤ T → ∀ P : Finset ℝ, IsSeparated 1 P →
      (∀ t ∈ P, t ∈ Set.Icc 0 T) → (∀ t ∈ P, (M : ℝ) ^ σ ≤ ‖smoothedPoly w M b t‖) →
      (P.card : ℝ) ≤ (T / (M : ℝ) ^ (6 / 5 : ℝ) + 2) * (2 * (((M : ℝ) ^ (6 / 5 : ℝ)) ^ ε₀ + 1)) *
        ((M : ℝ) ^ (6 / 5 : ℝ) * (M : ℝ) ^ ((12 - 20 * σ) / 5 + δ)) := by
  obtain ⟨M₀, hM₀⟩ := card_le_of_large_smoothedPoly w hw ε₀ hε₀ δ hδ
  refine ⟨max M₀ 1, ?_⟩
  intro M hM σ hσ b hb T hT P hP hPT hD
  have hM0 : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM1
  set L : ℝ := (M : ℝ) ^ (6 / 5 : ℝ) with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hMr (by norm_num)
  have hL0 : 0 < L := by linarith
  have hLe : 1 ≤ L ^ ε₀ := Real.one_le_rpow hL1 hε₀.le
  set q : ℕ := ⌈L ^ ε₀⌉₊ with hq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by
    rw [hq]; exact (Nat.ceil_pos.2 (by linarith)).ne')
  set B : ℝ := L * (M : ℝ) ^ ((12 - 20 * σ) / 5 + δ) with hB
  have hB0 : 0 ≤ B := by positivity
  set m : ℕ := ⌈T / L⌉₊ + 1 with hm
  have hmaps : ∀ t ∈ P, ⌊t / L⌋₊ ∈ Finset.range m := by
    intro t ht
    have ht' := hPT t ht
    simp only [Finset.mem_range, hm]
    have h1 : t / L ≤ T / L := div_le_div_of_nonneg_right ht'.2 hL0.le
    have h2 : ⌊t / L⌋₊ ≤ ⌈T / L⌉₊ :=
      (Nat.floor_le_floor h1).trans (Nat.floor_le_ceil _)
    omega
  have hfib : ∀ j ∈ Finset.range m, ((P.filter fun t => ⌊t / L⌋₊ = j).card : ℝ) ≤ 2 * q * B := by
    intro j hj
    set Pj := P.filter fun t => ⌊t / L⌋₊ = j with hPj
    have hsepj : IsSeparated 1 Pj := fun t ht t' ht' hne =>
      hP t (Finset.mem_filter.1 ht).1 t' (Finset.mem_filter.1 ht').1 hne
    obtain ⟨Q', hQ'sub, hQ'sep, hcard⟩ := exists_thin Pj hsepj q hq1
    have hsep' : IsSeparated (L ^ ε₀) Q' := by
      intro t ht t' ht' hne
      exact le_trans (Nat.le_ceil _) (hQ'sep t ht t' ht' hne)
    have hwin : ∀ t ∈ Q', t ∈ Set.Icc ((j : ℝ) * L) ((j : ℝ) * L + L) := by
      intro t ht
      have htj := Finset.mem_filter.1 (hQ'sub ht)
      have ht0 := (hPT t htj.1).1
      have h1 : ⌊t / L⌋₊ = j := htj.2
      have h2 := Nat.floor_le (div_nonneg ht0 hL0.le) 
      have h3 := Nat.lt_floor_add_one (t / L)
      rw [h1] at h2 h3
      constructor
      · have := (le_div_iff₀ hL0).1 h2
        linarith
      · have := (div_lt_iff₀ hL0).1 h3
        nlinarith
    have hDQ : ∀ t ∈ Q', (M : ℝ) ^ σ ≤ ‖smoothedPoly w M b t‖ := fun t ht =>
      hD t (Finset.mem_filter.1 (hQ'sub ht)).1
    have hbound := hM₀ M hM0 σ hσ b hb Q' ((j : ℝ) * L) hsep' hwin hDQ
    have hc : (Pj.card : ℝ) ≤ 2 * q * Q'.card := by exact_mod_cast hcard
    calc (Pj.card : ℝ) ≤ 2 * q * Q'.card := hc
      _ ≤ 2 * q * B := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
  have hsum : (P.card : ℝ) = ∑ j ∈ Finset.range m, ((P.filter fun t => ⌊t / L⌋₊ = j).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]; push_cast; rfl
  have hle : (P.card : ℝ) ≤ m * (2 * q * B) := by
    rw [hsum]
    calc _ ≤ ∑ j ∈ Finset.range m, 2 * (q:ℝ) * B := Finset.sum_le_sum hfib
      _ = m * (2 * q * B) := by simp
  have hm' : (m : ℝ) ≤ T / L + 2 := by
    have := Nat.ceil_lt_add_one (div_nonneg hT hL0.le)
    rw [hm]; push_cast; linarith
  have hq' : (q : ℝ) ≤ L ^ ε₀ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  calc (P.card : ℝ) ≤ m * (2 * q * B) := hle
    _ ≤ (T / L + 2) * (2 * (L ^ ε₀ + 1)) * B := by
      have h0 : (0:ℝ) ≤ 2 * q * B := by positivity
      have h1 : (m : ℝ) * (2 * q * B) ≤ (T / L + 2) * (2 * q * B) :=
        mul_le_mul_of_nonneg_right hm' h0
      have h2 : (T / L + 2) * (2 * q * B) ≤ (T / L + 2) * (2 * (L ^ ε₀ + 1) * B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hB0
        linarith
      nlinarith
    _ = _ := by rw [hB]

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

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

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

lemma rp_two {M N a c : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 * N) (ha : 0 ≤ a) (hc : (2:ℝ) ^ a ≤ c) :
    M ^ a ≤ c * N ^ a := by
  have hN0 : 0 ≤ N := by linarith
  calc M ^ a ≤ (2 * N) ^ a := Real.rpow_le_rpow hM0 hM ha
    _ = 2 ^ a * N ^ a := Real.mul_rpow (by norm_num) hN0
    _ ≤ c * N ^ a := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN0 _)

lemma two_rpow_le_two {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) : (2:ℝ) ^ a ≤ 2 := by
  calc (2:ℝ) ^ a ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = 2 := Real.rpow_one _

lemma two_rpow_le_32 {a : ℝ} (ha : a ≤ 5) : (2:ℝ) ^ a ≤ 32 := by
  calc (2:ℝ) ^ a ≤ 2 ^ (5:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = 32 := by norm_num

lemma final_calc {N M V T X ε₀ δ σ : ℝ} (hN : 1 ≤ N) (hNT : N ≤ T) (hM1 : 1 ≤ M)
    (hMN : M ≤ 2 * N) (hε : 0 < ε₀) (hε1 : ε₀ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hV : 0 < V)
    (hσ : M ^ σ = V / 3)
    (hX : X ≤ (T / M ^ (6 / 5 : ℝ) + 2) * (2 * ((M ^ (6 / 5 : ℝ)) ^ ε₀ + 1)) *
      (M ^ (6 / 5 : ℝ) * M ^ ((12 - 20 * σ) / 5 + δ))) :
    X ≤ 62208 * N ^ (δ + 6 / 5 * ε₀) * (T * N ^ (12 / 5 : ℝ) + N ^ (18 / 5 : ℝ)) / V ^ 4 := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := M ^ (6 / 5 : ℝ) with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hM1 (by norm_num)
  have hL0 : 0 < L := by linarith
  have hMσ : 0 < M ^ σ := Real.rpow_pos_of_pos hM0 _
  -- step 1
  have hLM : L * M ^ ((12 - 20 * σ) / 5 + δ) = 81 * M ^ (18 / 5 + δ) / V ^ 4 := by
    have hV3 : V = 3 * M ^ σ := by linarith
    have h4 : V ^ 4 = 81 * M ^ (4 * σ) := by
      have : (M ^ σ) ^ (4:ℕ) = M ^ (4 * σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; congr 1; push_cast; ring
      rw [hV3, mul_pow, this]; norm_num
    have h5 : M ^ (18 / 5 + δ) = L * M ^ ((12 - 20 * σ) / 5 + δ) * M ^ (4 * σ) := by
      rw [hL, ← Real.rpow_add hM0, ← Real.rpow_add hM0]; congr 1; ring
    rw [h4, h5]
    have : 0 < M ^ (4 * σ) := Real.rpow_pos_of_pos hM0 _
    field_simp
  -- step 2
  have hA : (T / L + 2) * M ^ (18 / 5 + δ) = T * M ^ (12 / 5 + δ) + 2 * M ^ (18 / 5 + δ) := by
    have : M ^ (18 / 5 + δ) = L * M ^ (12 / 5 + δ) := by
      rw [hL, ← Real.rpow_add hM0]; congr 1; ring
    rw [this]; field_simp
  -- step 3
  have hB1 : M ^ (12 / 5 + δ) ≤ 32 * (N ^ (12 / 5 : ℝ) * N ^ δ) := by
    rw [← Real.rpow_add hN0]
    exact rp_two hM0.le hMN (by linarith) (two_rpow_le_32 (by linarith))
  have hB2 : M ^ (18 / 5 + δ) ≤ 32 * (N ^ (18 / 5 : ℝ) * N ^ δ) := by
    rw [← Real.rpow_add hN0]
    exact rp_two hM0.le hMN (by linarith) (two_rpow_le_32 (by linarith))
  -- step 4
  have hC : 2 * (L ^ ε₀ + 1) ≤ 12 * N ^ (6 / 5 * ε₀) := by
    have h1 : 1 ≤ L ^ ε₀ := Real.one_le_rpow hL1 hε.le
    have h2 : L ^ ε₀ = M ^ (6 / 5 * ε₀) := by rw [hL, ← Real.rpow_mul hM0.le]
    have h3 : M ^ (6 / 5 * ε₀) ≤ 3 * N ^ (6 / 5 * ε₀) :=
      rp_two hM0.le hMN (by positivity) (by
        calc (2:ℝ) ^ (6 / 5 * ε₀) ≤ 2 ^ (6 / 5 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ ≤ 3 := by
            have : (2:ℝ) ^ (6 / 5 : ℝ) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            have h22 : (2:ℝ) ^ (2:ℝ) = 4 := by norm_num
            -- 2^(6/5) ≤ 3 since 2^6 ≤ 3^5
            have h6 : ((2:ℝ) ^ (6 / 5 : ℝ)) ^ 5 = 64 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
            by_contra hcon
            push Not at hcon
            have : (3:ℝ) ^ 5 < ((2:ℝ) ^ (6 / 5 : ℝ)) ^ 5 := by
              apply pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
            rw [h6] at this; norm_num at this)
    nlinarith
  have hNpos : 0 < N ^ (6 / 5 * ε₀) := Real.rpow_pos_of_pos hN0 _
  -- assemble
  have hVp : 0 < V ^ 4 := by positivity
  have hq : X ≤ (T / L + 2) * (2 * (L ^ ε₀ + 1)) * (81 * M ^ (18 / 5 + δ) / V ^ 4) := by
    rw [← hLM]; exact hX
  have hrhs : (T / L + 2) * (2 * (L ^ ε₀ + 1)) * (81 * M ^ (18 / 5 + δ) / V ^ 4) =
      (2 * (L ^ ε₀ + 1)) * 81 * ((T / L + 2) * M ^ (18 / 5 + δ)) / V ^ 4 := by ring
  rw [hrhs, hA] at hq
  have hMs : T * M ^ (12 / 5 + δ) + 2 * M ^ (18 / 5 + δ) ≤
      64 * N ^ δ * (T * N ^ (12 / 5 : ℝ) + N ^ (18 / 5 : ℝ)) := by
    have hNd : 0 < N ^ δ := Real.rpow_pos_of_pos hN0 _
    have e1 : T * M ^ (12 / 5 + δ) ≤ T * (32 * (N ^ (12 / 5 : ℝ) * N ^ δ)) :=
      mul_le_mul_of_nonneg_left hB1 hT0.le
    have e2 : 2 * M ^ (18 / 5 + δ) ≤ 2 * (32 * (N ^ (18 / 5 : ℝ) * N ^ δ)) := by linarith
    have hpos : 0 ≤ T * (N ^ (12 / 5 : ℝ) * N ^ δ) := by positivity
    linarith [e1, e2, hpos]
  have hNN : N ^ (6 / 5 * ε₀) * N ^ δ = N ^ (δ + 6 / 5 * ε₀) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hS0 : 0 ≤ T * M ^ (12 / 5 + δ) + 2 * M ^ (18 / 5 + δ) := by positivity
  calc X ≤ (2 * (L ^ ε₀ + 1)) * 81 * (T * M ^ (12 / 5 + δ) + 2 * M ^ (18 / 5 + δ)) / V ^ 4 := hq
    _ ≤ (12 * N ^ (6 / 5 * ε₀)) * 81 * (64 * N ^ δ * (T * N ^ (12 / 5 : ℝ) + N ^ (18 / 5 : ℝ))) / V ^ 4 := by
      apply div_le_div_of_nonneg_right _ hVp.le
      apply mul_le_mul _ hMs hS0 (by positivity)
      exact mul_le_mul_of_nonneg_right hC (by norm_num)
    _ = 62208 * N ^ (δ + 6 / 5 * ε₀) * (T * N ^ (12 / 5 : ℝ) + N ^ (18 / 5 : ℝ)) / V ^ 4 := by
      rw [← hNN]; ring

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

open GuthMaynard Complex

theorem hard (w : ℝ → ℝ) (hw : IsWeight w) (ε₀ δ : ℝ) (h0 : 0 < ε₀) (hε1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N₁ : ℕ, ∀ (T : ℝ) (N : ℕ), N₁ ≤ N → (N : ℝ) ≤ T → ∀ (V : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      12 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) / 12 →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ 200000 * (N : ℝ) ^ (δ + 6 / 5 * ε₀) *
        (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4 := by
  obtain ⟨M₀, hM₀⟩ := piece w hw ε₀ h0 δ hδ
  refine ⟨max 6 (2 * M₀), ?_⟩
  intro T N hN hNT V b hb hV1 hV2 R t hsep htT hV
  have hN6 : 6 ≤ N := le_trans (le_max_left _ _) hN
  have hNM : 2 * M₀ ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (6:ℝ) ≤ N := by exact_mod_cast hN6
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hVp : 0 < V := by
    have : 0 < 12 * (N : ℝ) ^ (7 / 10 : ℝ) := by positivity
    linarith
  have hT0 : 0 < T := by linarith
  by_cases hR : R = 0
  · subst hR
    simp only [Nat.cast_zero]
    positivity
  obtain ⟨M, A, hMA, hsum⟩ := pieces N hN6
  -- every point has a piece with value at least V/3
  have hex : ∀ r, ∃ i : Fin 3, V / 3 ≤ ‖∑ n ∈ A i, b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖ := by
    intro r
    by_contra hcon
    push Not at hcon
    have h := hV r
    rw [hsum (fun n => b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I))] at h
    have h2 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun i => ∑ n ∈ A i, b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I))
    have h3 : ∑ i : Fin 3, ‖∑ n ∈ A i, b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖ < V := by
      rw [Fin.sum_univ_three]
      have := hcon 0; have := hcon 1; have := hcon 2
      linarith
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
  have hMr1 : (1:ℝ) ≤ M i := by exact_mod_cast hMpos
  have hMr0 : (0:ℝ) < M i := by linarith
  have hMN' : (M i : ℝ) ≤ 2 * N := by exact_mod_cast hMN
  have hNM' : (N : ℝ) ≤ 2 * M i := by exact_mod_cast hM2N
  -- σ
  set σ : ℝ := Real.logb (M i) (V / 3) with hσdef
  have hMi1 : (1:ℝ) < M i := by
    have : 2 ≤ M i := by omega
    exact_mod_cast this
  have hσM : (M i : ℝ) ^ σ = V / 3 := Real.rpow_logb hMr0 hMi1.ne' (by positivity)
  have hσ1 : 7 / 10 ≤ σ := by
    rw [hσdef, Real.le_logb_iff_rpow_le hMi1 (by positivity)]
    have := rp_two hMr0.le hMN' (by norm_num : (0:ℝ) ≤ 7 / 10) (two_rpow_le_two (by norm_num) (by norm_num))
    have hNp : 0 < (N:ℝ) ^ (7 / 10 : ℝ) := by positivity
    linarith
  have hσ2 : σ ≤ 8 / 10 := by
    rw [hσdef, Real.logb_le_iff_le_rpow hMi1 (by positivity)]
    have := rp_two (by linarith : (0:ℝ) ≤ N) hNM' (by norm_num : (0:ℝ) ≤ 4 / 5) (two_rpow_le_two (by norm_num) (by norm_num))
    have hNp : 0 < (N:ℝ) ^ (4 / 5 : ℝ) := by positivity
    norm_num at this ⊢
    linarith
  have hDP : ∀ x ∈ P, (M i : ℝ) ^ σ ≤
      ‖smoothedPoly w (M i) (fun n => if n ∈ A i then b n else 0) x‖ := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    rw [smoothed_eq w hw (M i) hMpos (A i) hAi b, hσM]
    have := hg r
    have hgr : g r = i := (Finset.mem_filter.1 hr).2
    rw [hgr] at this
    exact this
  have hpc := hM₀ (M i) (by omega) σ ⟨hσ1, hσ2⟩ _ (by
    intro n; show ‖if n ∈ A i then b n else 0‖ ≤ 1; split_ifs <;> simp [hb n]) T (by linarith [(htT ⟨0, hRpos⟩).1, (htT ⟨0, hRpos⟩).2]) P hPsep hPT hDP
  have hfc := final_calc (N := (N:ℝ)) (M := (M i : ℝ)) (V := V) (T := T) (X := (P.card : ℝ)) (ε₀ := ε₀)
    (δ := δ) (σ := σ) hN1 hNT hMr1 hMN' h0 hε1 hδ hδ1 hVp hσM hpc
  have hRR : (R : ℝ) ≤ 3 * (P.card : ℝ) := by
    rw [hPcard]; exact_mod_cast hRS
  have hpos : 0 ≤ (N : ℝ) ^ (δ + 6 / 5 * ε₀) *
        (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4 := by positivity
  have e : 62208 * (N : ℝ) ^ (δ + 6 / 5 * ε₀) * (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4 =
      62208 * ((N : ℝ) ^ (δ + 6 / 5 * ε₀) * (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4) := by ring
  have e' : 200000 * (N : ℝ) ^ (δ + 6 / 5 * ε₀) * (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4 =
      200000 * ((N : ℝ) ^ (δ + 6 / 5 * ε₀) * (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4) := by ring
  rw [e] at hfc
  rw [e']
  nlinarith

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

open GuthMaynard

lemma easy1 {T N V Q : ℝ} (hT : 0 < T) (hN : 1 ≤ N) (hV : 0 < V)
    (h : V ^ 2 ≤ Q * N ^ (7 / 5 : ℝ)) : T * N / V ^ 2 ≤ Q * (T * N ^ (12 / 5 : ℝ) / V ^ 4) := by
  have hN0 : 0 < N := by linarith
  have e : N ^ (12 / 5 : ℝ) = N * N ^ (7 / 5 : ℝ) := by
    rw [show (12 / 5 : ℝ) = 1 + 7 / 5 by norm_num, Real.rpow_add hN0, Real.rpow_one]
  rw [e, div_le_iff₀ (by positivity)]
  have h4 : Q * (T * (N * N ^ (7 / 5 : ℝ)) / V ^ 4) * V ^ 2 = T * N * (Q * N ^ (7 / 5 : ℝ)) / V ^ 2 := by
    field_simp
  rw [h4, le_div_iff₀ (by positivity)]
  have : 0 ≤ T * N := by positivity
  nlinarith

lemma easy2 {T N V Q : ℝ} (hT : 0 < T) (hN : 1 ≤ N) (hV : 0 < V)
    (h : N ^ (8 / 5 : ℝ) ≤ Q * V ^ 2) : T * (N ^ 4 / V ^ 6) ≤ Q * (T * N ^ (12 / 5 : ℝ) / V ^ 4) := by
  have hN0 : 0 < N := by linarith
  have e : N ^ 4 = N ^ (12 / 5 : ℝ) * N ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_natCast]; norm_num
  rw [e]
  have hp : 0 < N ^ (12 / 5 : ℝ) := by positivity
  have : T * (N ^ (12 / 5 : ℝ) * N ^ (8 / 5 : ℝ) / V ^ 6) =
      T * N ^ (12 / 5 : ℝ) / V ^ 4 * (N ^ (8 / 5 : ℝ) / V ^ 2) := by field_simp
  rw [this]
  have h2 : N ^ (8 / 5 : ℝ) / V ^ 2 ≤ Q := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h3 : 0 ≤ T * N ^ (12 / 5 : ℝ) / V ^ 4 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
theorem card_le_of_large_values_dev :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 +
        T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  intro ε hε
  obtain ⟨w, hw⟩ := exists_weight
  set κ : ℝ := min ε 1 with hκ
  have hκ0 : 0 < κ := lt_min hε one_pos
  have hκε : κ ≤ ε := min_le_left _ _
  have hκ1 : κ ≤ 1 := min_le_right _ _
  obtain ⟨T₁, hT₁⟩ := card_le_of_large_values_classical (κ / 2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hard w hw (κ / 5) (κ / 4) (by positivity) (by linarith) (by positivity) (by linarith)
  set Cb : ℝ := 200000 + 4 * N₁ with hCb
  have hCb0 : 200000 ≤ Cb := by rw [hCb]; have : (0:ℝ) ≤ N₁ := Nat.cast_nonneg _; linarith
  have ev1 : ∀ᶠ T : ℝ in Filter.atTop, Cb ≤ T ^ (κ / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < κ / 2)).eventually_ge_atTop _
  have ev2 : ∀ᶠ T : ℝ in Filter.atTop, max T₁ 1 ≤ T := Filter.eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (ev1.and ev2)
  refine ⟨T₀, ?_⟩
  intro T hT N hN V hV b hb R t hsep htT hVt
  obtain ⟨hCT, hT1'⟩ := hT₀ T hT
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT1'
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT1'
  have hT0 : 0 < T := by linarith
  set E : ℝ := T ^ (κ / 2) with hE
  have hE1 : 1 ≤ E := Real.one_le_rpow hT1 (by positivity)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N:ℝ) := by linarith
  set a : ℝ := (N:ℝ) ^ 2 / V ^ 2 with ha
  set c : ℝ := (N:ℝ) ^ (18 / 5 : ℝ) / V ^ 4 with hc
  set d : ℝ := T * (N:ℝ) ^ (12 / 5 : ℝ) / V ^ 4 with hd
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hd0 : 0 ≤ d := by positivity
  -- the final step: R ≤ E * Cb * (a + c + d) suffices
  suffices key : (R : ℝ) ≤ E * Cb * (a + c + d) by
    have hTκ : T ^ κ ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 hκε
    have hEE : E * E = T ^ κ := by
      rw [hE, ← Real.rpow_add hT0]; congr 1; ring
    have hs : 0 ≤ a + c + d := by positivity
    calc (R : ℝ) ≤ E * Cb * (a + c + d) := key
      _ ≤ E * E * (a + c + d) := by
        apply mul_le_mul_of_nonneg_right _ hs
        exact mul_le_mul_of_nonneg_left hCT (by linarith)
      _ ≤ T ^ ε * (a + c + d) := by
        rw [hEE]; exact mul_le_mul_of_nonneg_right hTκ hs
  by_cases hR : R = 0
  · subst hR; simp only [Nat.cast_zero]; positivity
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  have hcl := hT₁ T hTT₁ N hN V hV b hb R t hsep htT hVt
  rw [← hE] at hcl
  have hkey1 : (R : ℝ) ≤ E * (a + T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hcl
  have hm1 : T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) / V ^ 2) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hT0.le
  have hm2 : T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) ^ 4 / V ^ 6) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hT0.le
  have hTN : T * ((N : ℝ) / V ^ 2) = T * N / V ^ 2 := by ring
  -- a general finishing step
  have fin : ∀ Q : ℝ, 1 ≤ Q → Q + 1 ≤ Cb → T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ Q * (a + c + d) →
      (R : ℝ) ≤ E * Cb * (a + c + d) := by
    intro Q hQ1 hQ hQb
    have hs : 0 ≤ a + c + d := by positivity
    calc (R : ℝ) ≤ E * (a + T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hkey1
      _ ≤ E * (a + Q * (a + c + d)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
      _ ≤ E * ((Cb) * (a + c + d)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have haS : a ≤ a + c + d := by linarith
        have := mul_le_mul_of_nonneg_right hQ hs
        nlinarith
      _ = E * Cb * (a + c + d) := by ring
  by_cases hB : T ≤ (N : ℝ)
  · -- N ≥ T
    refine fin 2 (by norm_num) (by linarith) ?_
    calc T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) / V ^ 2) := hm1
      _ ≤ (N : ℝ) * ((N : ℝ) / V ^ 2) := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = a := by rw [ha]; ring
      _ ≤ 2 * (a + c + d) := by linarith
  push Not at hB
  by_cases hH : N₁ ≤ N
  · by_cases hlo : V < 12 * (N : ℝ) ^ (7 / 10 : ℝ)
    · refine fin 144 (by norm_num) (by linarith) ?_
      have h2 : V ^ 2 ≤ 144 * (N : ℝ) ^ (7 / 5 : ℝ) := by
        have : (N : ℝ) ^ (7 / 5 : ℝ) = ((N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        rw [this]
        have hp : 0 ≤ (N : ℝ) ^ (7 / 10 : ℝ) := by positivity
        nlinarith
      have := easy1 hT0 hNr hV h2
      calc T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) / V ^ 2) := hm1
        _ = T * N / V ^ 2 := hTN
        _ ≤ 144 * d := this
        _ ≤ 144 * (a + c + d) := by linarith
    push Not at hlo
    by_cases hhi : (N : ℝ) ^ (4 / 5 : ℝ) / 12 < V
    · refine fin 144 (by norm_num) (by linarith) ?_
      have h2 : (N : ℝ) ^ (8 / 5 : ℝ) ≤ 144 * V ^ 2 := by
        have : (N : ℝ) ^ (8 / 5 : ℝ) = ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        rw [this]
        have hp : 0 ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by positivity
        nlinarith
      have := easy2 hT0 hNr hV h2
      calc T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) ^ 4 / V ^ 6) := hm2
        _ ≤ 144 * d := this
        _ ≤ 144 * (a + c + d) := by linarith
    push Not at hhi
    -- hard range
    have hh := hN₁ T N hH hB.le V b hb hlo hhi R t hsep htT hVt
    have hx : (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) ≤ E := by
      calc (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) ≤ T ^ (κ / 4 + 6 / 5 * (κ / 5)) :=
            Real.rpow_le_rpow hN0.le hB.le (by positivity)
        _ ≤ T ^ (κ / 2) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have e : 200000 * (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) * (T * (N : ℝ) ^ (12 / 5 : ℝ) + (N : ℝ) ^ (18 / 5 : ℝ)) / V ^ 4 =
        200000 * (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) * (d + c) := by
      rw [hd, hc]; field_simp
    rw [e] at hh
    have hs : 0 ≤ d + c := by positivity
    have hnn : 0 ≤ (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) := by positivity
    calc (R : ℝ) ≤ 200000 * (N : ℝ) ^ (κ / 4 + 6 / 5 * (κ / 5)) * (d + c) := hh
      _ ≤ 200000 * E * (d + c) := by
        apply mul_le_mul_of_nonneg_right _ hs; linarith
      _ ≤ E * Cb * (a + c + d) := by
        have h1 : 200000 * (d + c) ≤ Cb * (a + c + d) := by
          have h2 : 200000 * (d + c) ≤ Cb * (d + c) := mul_le_mul_of_nonneg_right hCb0 hs
          have h3 : Cb * (d + c) ≤ Cb * (a + c + d) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          linarith
        have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ E)
        calc 200000 * E * (d + c) = E * (200000 * (d + c)) := by ring
          _ ≤ E * (Cb * (a + c + d)) := h4
          _ = E * Cb * (a + c + d) := by ring
  · -- small N
    push Not at hH
    have hNN₁ : (N : ℝ) + 1 ≤ N₁ := by exact_mod_cast hH
    refine fin (4 * N₁) (by
      have : (1:ℝ) ≤ N := hNr
      linarith) (by rw [hCb]; linarith) ?_
    have hV2 : V ≤ 2 * N := by
      have hr := hVt ⟨0, hRpos⟩
      refine hr.trans ?_
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Finset.Icc N (2 * N), ‖b n * (n : ℂ) ^ (((t ⟨0, hRpos⟩ : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
        intro n hn
        have hn0 : 0 < n := by have := (Finset.mem_Icc.1 hn).1; omega
        rw [norm_mul]
        have h1 : ‖(n : ℂ) ^ (((t ⟨0, hRpos⟩ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
          rw [Complex.norm_cpow_of_ne_zero (by exact_mod_cast hn0.ne')]
          simp
        rw [h1]; simpa using hb n
      refine (Finset.sum_le_card_nsmul _ _ 1 this).trans ?_
      simp only [Nat.card_Icc, nsmul_eq_mul, mul_one]
      have : ((2 * N + 1 - N : ℕ) : ℝ) = N + 1 := by
        rw [show 2 * N + 1 - N = N + 1 by omega]; push_cast; ring
      rw [this]; linarith
    have h2 : V ^ 2 ≤ (4 * N₁) * (N : ℝ) ^ (7 / 5 : ℝ) := by
      have e : (N : ℝ) ^ 2 = (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (7 / 5 : ℝ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_natCast]; norm_num
      have h35 : (N : ℝ) ^ (3 / 5 : ℝ) ≤ N₁ := by
        calc (N : ℝ) ^ (3 / 5 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
          _ = N := Real.rpow_one _
          _ ≤ N₁ := by linarith
      have hp : 0 ≤ (N : ℝ) ^ (7 / 5 : ℝ) := by positivity
      have : V ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      rw [e] at this
      nlinarith [mul_le_mul_of_nonneg_right h35 hp]
    have := easy1 hT0 hNr hV h2
    calc T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) ≤ T * ((N : ℝ) / V ^ 2) := hm1
      _ = T * N / V ^ 2 := hTN
      _ ≤ (4 * N₁) * d := this
      _ ≤ (4 * N₁) * (a + c + d) := by
        have : (0:ℝ) ≤ 4 * N₁ := by positivity
        nlinarith

end GuthMaynardGoal

end
end

section
open GuthMaynard

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 +
        T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  apply GuthMaynardGoal.card_le_of_large_values_dev <;> assumption

end
