-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values_of_five_sixths
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:41:01.188311+00:00
-- url     : https://prove2.me/submissions/a3d609bc-798c-4d0b-b211-e161beac4c8d

import Mathlib
import Theorems.Thm_GuthMaynard_card_le_of_large_values_twelve_one
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_card_le_of_large_values_classical
import Theorems.Thm_GuthMaynard_card_le_of_large_values_jutila


section
namespace GuthMaynardS1213.P121
open GuthMaynard
/-!
Blueprint for Proposition 12.1 (`GuthMaynard.card_le_of_large_values_of_five_sixths`).

* `twelve_one` : the eight-term bound (12.1) for a fixed `k`, for any `T` with `T^{5/6} ≤ N ≤ T`
  (Part A: three smoothed pieces, thinning, Props 4.6, 5.1, 6.1, 11.2, self-bounding algebra).
* `classical_Ioc` : (1.1) for sums over `N < n ≤ 2N` (Part B, from the published (1.1)).
* `jutila_Ioc` : Jutila's estimate with `k = 3`, `V = N^σ` (Part B, from the published Jutila).
* `card_le_of_large_values_of_five_sixths_dev` : the target, from the three stubs (Part B).
-/
alias twelve_one := GuthMaynard.card_le_of_large_values_twelve_one

end GuthMaynardS1213.P121
end

section
namespace GuthMaynardS1213.P121.PartB
open GuthMaynard Complex
/-! ## (1.1) over `Ioc` -/
theorem classical_Ioc :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := GuthMaynard.card_le_of_large_values_classical ε hε
  refine ⟨T₀, fun T hT N hN V hV b hb R t hsep ht hlarge => ?_⟩
  let b' : ℕ → ℂ := fun n => if n = N then 0 else b n
  have hb' : ∀ n, ‖b' n‖ ≤ 1 := by
    intro n; by_cases h : n = N <;> simp [b', h, hb n]
  refine hT₀ T hT N hN V hV b' hb' R t hsep ht (fun r => ?_)
  have hsum : ∑ n ∈ Finset.Icc N (2 * N), b' n * (n : ℂ) ^ ((t r : ℂ) * Complex.I) =
      ∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I) := by
    rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
    simp only [b', if_pos rfl, zero_mul, zero_add]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have : n ≠ N := by
      intro h; rw [Finset.mem_Ioc] at hn; omega
    simp [this]
  rw [hsum]; exact hlarge r

end GuthMaynardS1213.P121.PartB
end

section
namespace GuthMaynardS1213.P121
open GuthMaynard

end GuthMaynardS1213.P121
end

section
namespace GuthMaynardS1213.P121.PartB
open GuthMaynard Complex
/-! ## Jutila with `k = 3` over `Ioc` -/
theorem jutila_Ioc :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ σ : ℝ,
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ ((10 - 16 * σ) / 3) +
        T * (N : ℝ) ^ (18 - 24 * σ)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := GuthMaynard.card_le_of_large_values_jutila ε hε 3 (by norm_num)
  refine ⟨max C 0, fun T hT N hN σ b hb R t hsep ht hlarge => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  set V : ℝ := (N : ℝ) ^ σ with hVdef
  have hV : 0 < V := Real.rpow_pos_of_pos hN0 σ
  have key := hC T hT N hN b V hV R (fun r => -((t r : ℂ) * I))
    (fun r => by simp)
    (fun r q => by
      have h1 := ht r; have h2 := ht q
      simp only [Set.mem_Icc] at h1 h2
      simp only [neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [abs_le]; constructor <;> linarith)
    (fun r q hrq => by
      simp only [neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [neg_sub_neg, abs_sub_comm]; exact hsep r q hrq)
    (fun r => by simpa only [neg_neg] using hlarge r)
  simp only at key
  set G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 with hGdef
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun n _ => by positivity)
  have hGN : G ≤ N := by
    calc G ≤ ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => by
            have := hb n; have := norm_nonneg (b n); nlinarith)
      _ = N := by simp [Nat.card_Ioc]; omega
  -- the three terms
  have hV2 : V ^ 2 = (N : ℝ) ^ (2 * σ) := by
    rw [hVdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have t1 : G * N / V ^ 2 ≤ (N : ℝ) ^ (2 - 2 * σ) := by
    rw [hV2, Real.rpow_sub hN0, Real.rpow_two]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have t2 : T * G ^ (3 - 1 / ((3 : ℕ) : ℝ)) * (N : ℝ) ^ (1 - 1 / ((3 : ℕ) : ℝ)) *
      V ^ (-6 + 2 / ((3 : ℕ) : ℝ)) ≤ T * (N : ℝ) ^ ((10 - 16 * σ) / 3) := by
    have e1 : (3 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 8 / 3 := by norm_num
    have e2 : (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 2 / 3 := by norm_num
    have e3 : (-6 : ℝ) + 2 / ((3 : ℕ) : ℝ) = -16 / 3 := by norm_num
    rw [e1, e2, e3, hVdef, ← Real.rpow_mul hN0.le]
    rw [show T * G ^ (8 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (σ * (-16 / 3)) =
      T * (G ^ (8 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (σ * (-16 / 3))) by ring]
    apply mul_le_mul_of_nonneg_left _ hT0.le
    calc G ^ (8 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (σ * (-16 / 3))
        ≤ (N : ℝ) ^ (8 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (σ * (-16 / 3)) := by
          gcongr
      _ = (N : ℝ) ^ ((10 - 16 * σ) / 3) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  have t3 : T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ 3 ≤ T * (N : ℝ) ^ (18 - 24 * σ) := by
    apply mul_le_mul_of_nonneg_left _ hT0.le
    have hV8 : V ^ 8 = (N : ℝ) ^ (8 * σ) := by
      rw [hVdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have h1 : G ^ 4 * (N : ℝ) ^ 2 / V ^ 8 ≤ (N : ℝ) ^ (6 - 8 * σ) := by
      rw [hV8, Real.rpow_sub hN0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (N : ℝ) ^ (6 : ℝ) = (N : ℝ) ^ 4 * (N : ℝ) ^ 2 := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [this]; gcongr
    calc (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ 3 ≤ ((N : ℝ) ^ (6 - 8 * σ)) ^ 3 := by
          gcongr
      _ = (N : ℝ) ^ (18 - 24 * σ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hsum0 : 0 ≤ (N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ ((10 - 16 * σ) / 3) +
      T * (N : ℝ) ^ (18 - 24 * σ) := by positivity
  have hTε : 0 ≤ T ^ ε := by positivity
  calc (R : ℝ) ≤ C * (G * N / V ^ 2 + T * G ^ (3 - 1 / ((3 : ℕ) : ℝ)) *
        (N : ℝ) ^ (1 - 1 / ((3 : ℕ) : ℝ)) * V ^ (-6 + 2 / ((3 : ℕ) : ℝ)) +
        T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ 3) * T ^ ε := key
    _ ≤ max C 0 * (G * N / V ^ 2 + T * G ^ (3 - 1 / ((3 : ℕ) : ℝ)) *
        (N : ℝ) ^ (1 - 1 / ((3 : ℕ) : ℝ)) * V ^ (-6 + 2 / ((3 : ℕ) : ℝ)) +
        T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ 3) * T ^ ε := by
        have hX : 0 ≤ G * N / V ^ 2 + T * G ^ (3 - 1 / ((3 : ℕ) : ℝ)) *
            (N : ℝ) ^ (1 - 1 / ((3 : ℕ) : ℝ)) * V ^ (-6 + 2 / ((3 : ℕ) : ℝ)) +
            T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) hTε
    _ ≤ max C 0 * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ ((10 - 16 * σ) / 3) +
        T * (N : ℝ) ^ (18 - 24 * σ)) * T ^ ε := by
        apply mul_le_mul_of_nonneg_right _ hTε
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        linarith
    _ = max C 0 * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ ((10 - 16 * σ) / 3) +
        T * (N : ℝ) ^ (18 - 24 * σ)) := by ring

end GuthMaynardS1213.P121.PartB
end

section
namespace GuthMaynardS1213.P121
open GuthMaynard

end GuthMaynardS1213.P121
end

section
namespace GuthMaynardS1213.P121.PartB
open GuthMaynard Complex
/-! ## Infrastructure -/
/-- The large-values hypothesis bundle. -/
def Large (T : ℝ) (N : ℕ) (σ : ℝ) (R : ℕ) : Prop :=
  ∃ (b : ℕ → ℂ) (t : Fin R → ℝ), (∀ n, ‖b n‖ ≤ 1) ∧ (∀ r s, r ≠ s → 1 ≤ |t r - t s|) ∧
    (∀ r, t r ∈ Set.Icc 0 T) ∧
    (∀ r, (N : ℝ) ^ σ ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖)

/-- The `k`-dependent pair of terms. -/
noncomputable def Fk (T y σ : ℝ) (k : ℕ) : ℝ :=
  T ^ ((k : ℝ) / (k + 1)) * y ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
    y ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3))

lemma cN {T y x : ℝ} (hT : 0 < T) (hy : y = T ^ x) (b : ℝ) : y ^ b = T ^ (x * b) := by
  rw [hy, ← Real.rpow_mul hT.le]

lemma cTT {T : ℝ} (hT : 0 < T) (a c : ℝ) : T ^ a * T ^ c = T ^ (a + c) :=
  (Real.rpow_add hT a c).symm

lemma cT1 {T : ℝ} (hT : 0 < T) (c : ℝ) : T * T ^ c = T ^ (1 + c) := by
  rw [Real.rpow_add hT, Real.rpow_one]

lemma pmono {T a b : ℝ} (hT : 1 ≤ T) (h : a ≤ b) : T ^ a ≤ T ^ b :=
  Real.rpow_le_rpow_of_exponent_le hT h

lemma setup {T : ℝ} (hT : 2 ≤ T) {N : ℕ} (hN : (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T) :
    ∃ x : ℝ, (N : ℝ) = T ^ x ∧ 5 / 6 ≤ x ∧ x ≤ 1 ∧ 2 ≤ N := by
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have h56 : 1 < T ^ (5 / 6 : ℝ) := Real.one_lt_rpow hT1 (by norm_num)
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le h56 hN.1
  have hN2 : 2 ≤ N := by
    have : 1 < N := by exact_mod_cast hN1
    omega
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨Real.logb T N, (Real.rpow_logb hT0 hT1.ne' hN0).symm, ?_, ?_, hN2⟩
  · rw [← Real.rpow_le_rpow_left_iff hT1, Real.rpow_logb hT0 hT1.ne' hN0]; exact hN.1
  · rw [← Real.rpow_le_rpow_left_iff hT1, Real.rpow_logb hT0 hT1.ne' hN0, Real.rpow_one]
    exact hN.2

lemma large_zero {T σ : ℝ} {N R : ℕ} (hN : 2 ≤ N) (hs : 1 < σ) (hL : Large T N σ R) :
    R = 0 := by
  obtain ⟨b, t, hb, -, -, hl⟩ := hL
  by_contra hR
  have r : Fin R := ⟨0, Nat.pos_of_ne_zero hR⟩
  have h1 := hl r
  have h2 : ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Ioc N (2 * N), ‖b n * (n : ℂ) ^ ((t r : ℂ) * I)‖
        ≤ ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro n hn
          have hn0 : 0 < n := by rw [Finset.mem_Ioc] at hn; omega
          rw [norm_mul, norm_natCast_cpow_of_pos hn0]
          simpa using hb n
      _ = N := by simp [Nat.card_Ioc]; omega
  have h3 : (N : ℝ) < (N : ℝ) ^ σ := by
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have : (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt hN1 hs
    simpa using this
  linarith

lemma npow_div {y : ℝ} (hy : 0 < y) (m j : ℕ) (σ : ℝ) :
    y ^ m / (y ^ σ) ^ j = y ^ ((m : ℝ) - j * σ) := by
  rw [Real.rpow_sub hy, Real.rpow_natCast, ← Real.rpow_natCast (y ^ σ),
    ← Real.rpow_mul hy.le, mul_comm σ]

lemma large_classical (ε : ℝ) (hε : 0 < ε) : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    ∀ N : ℕ, 1 ≤ N → ∀ (σ : ℝ) (R : ℕ), Large T N σ R →
    (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ (1 - 2 * σ)) ∧
    (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ (4 - 6 * σ)) := by
  obtain ⟨T₀, h⟩ := classical_Ioc ε hε
  refine ⟨max T₀ 1, le_max_right _ _, fun T hT N hN σ R hL => ?_⟩
  obtain ⟨b, t, hb, hsep, ht, hl⟩ := hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : 0 ≤ T := by linarith [le_max_right T₀ 1]
  have key := h T (le_trans (le_max_left _ _) hT) N hN ((N : ℝ) ^ σ)
    (Real.rpow_pos_of_pos hN0 σ) b hb R t hsep ht hl
  have e2 : (N : ℝ) ^ 2 / ((N : ℝ) ^ σ) ^ 2 = (N : ℝ) ^ (2 - 2 * σ) := by
    rw [npow_div hN0 2 2 σ]; norm_num
  have e1 : (N : ℝ) / ((N : ℝ) ^ σ) ^ 2 = (N : ℝ) ^ (1 - 2 * σ) := by
    have := npow_div hN0 1 2 σ
    rw [pow_one] at this; rw [this]; norm_num
  have e4 : (N : ℝ) ^ 4 / ((N : ℝ) ^ σ) ^ 6 = (N : ℝ) ^ (4 - 6 * σ) := by
    rw [npow_div hN0 4 6 σ]; norm_num
  rw [e2, e1, e4] at key
  have hTε : 0 ≤ T ^ ε := by positivity
  constructor
  · refine key.trans (mul_le_mul_of_nonneg_left (add_le_add_right
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hT0) _) hTε)
  · refine key.trans (mul_le_mul_of_nonneg_left (add_le_add_right
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hT0) _) hTε)

lemma large_jutila (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ N : ℕ, 1 ≤ N → ∀ (σ : ℝ) (R : ℕ), Large T N σ R →
    (R : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T * (N : ℝ) ^ ((10 - 16 * σ) / 3) +
        T * (N : ℝ) ^ (18 - 24 * σ)) := by
  obtain ⟨C, h⟩ := jutila_Ioc ε hε
  refine ⟨max C 0, le_max_right _ _, fun T hT N hN σ R hL => ?_⟩
  obtain ⟨b, t, hb, hsep, ht, hl⟩ := hL
  have hT0 : 0 ≤ T := by linarith
  refine (h T hT N hN σ b hb R t hsep ht hl).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (by positivity)) (by positivity)

lemma large_twelve (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) : ∃ C T₀ : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T →
    ∀ (σ : ℝ) (R : ℕ), Large T N σ R →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (5 - 6 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
        T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T * (N : ℝ) ^ (9 / 2 - 7 * σ) + T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19)) := by
  obtain ⟨C, T₀, h⟩ := GuthMaynardS1213.P121.twelve_one k hk δ hδ
  refine ⟨max C 0, max T₀ 0, le_max_right _ _, fun T hT N hN σ R hL => ?_⟩
  obtain ⟨b, t, hb, hsep, ht, hl⟩ := hL
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  refine (h T (le_trans (le_max_left _ _) hT) N hN σ b hb R t hsep ht hl).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (by positivity)) (by positivity)

lemma fixed_k (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ 2 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T →
    ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 1 → ∀ R : ℕ, Large T N σ R → 1 ≤ k →
      (R : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        Fk T N σ k) := by
  by_cases hk : 1 ≤ k
  swap
  · exact ⟨0, 2, le_rfl, le_rfl, fun _ _ _ _ _ _ _ _ _ h => absurd h hk⟩
  obtain ⟨C₁, T₁, hC₁, h12⟩ := large_twelve k hk ε hε
  obtain ⟨T₂, hT₂, hcl⟩ := large_classical ε hε
  refine ⟨6 * C₁ + 1, max (max T₁ T₂) 2, by positivity, le_max_right _ _, ?_⟩
  intro T hT N hN σ hs1 hs2 R hL _
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT2' : 2 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨x, hy, hx1, hx2, hN2⟩ := setup hT2' hN
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hTε : 0 ≤ T ^ ε := by positivity
  have hQ : 0 ≤ C₁ * T ^ ε := by positivity
  simp only [Fk]
  by_cases hcase : x * (5 - 6 * σ) ≤ 1 / 2 + x * (3 - 4 * σ)
  · have h := h12 T hT1 N hN σ R hL
    simp only [cN hT0 hy, cTT hT0, cT1 hT0] at h ⊢
    have e1 : T ^ (x * (5 - 6 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := pmono hTone hcase
    have e2 : T ^ (4 / 3 + x * (2 - 4 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) :=
      pmono hTone (by nlinarith)
    have e3 : T ^ (1 + x * (9 / 2 - 7 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) :=
      pmono hTone (by nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hs1)])
    have e4 : T ^ (18 / 19 + x * (72 / 19 - 112 * σ / 19)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) :=
      pmono hTone (by nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hs1)])
    have p1 : 0 ≤ T ^ (x * (2 - 2 * σ)) := by positivity
    have p2 : 0 ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := by positivity
    have p3 : 0 ≤ T ^ ((k : ℝ) / (k + 1) + x * ((4 - 6 * σ) * ((k : ℝ) / (k + 1)))) := by
      positivity
    have p4 : 0 ≤ T ^ (x * ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) + 2 / (4 * (k : ℝ) + 3)) := by
      positivity
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left e1 hQ, mul_le_mul_of_nonneg_left e2 hQ,
      mul_le_mul_of_nonneg_left e3 hQ, mul_le_mul_of_nonneg_left e4 hQ,
      mul_nonneg hQ p1, mul_nonneg hQ p2, mul_nonneg hQ p3, mul_nonneg hQ p4,
      mul_nonneg hTε p1, mul_nonneg hTε p2, mul_nonneg hTε p3, mul_nonneg hTε p4]
  · have hc : 1 + x * (1 - 2 * σ) ≤ 1 / 2 + x * (3 - 4 * σ) := by linarith
    have h := (hcl T hT2 N (by omega) σ R hL).1
    simp only [cN hT0 hy, cTT hT0, cT1 hT0] at h ⊢
    have e1 : T ^ (1 + x * (1 - 2 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := pmono hTone hc
    have p1 : 0 ≤ T ^ (x * (2 - 2 * σ)) := by positivity
    have p2 : 0 ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := by positivity
    have p3 : 0 ≤ T ^ ((k : ℝ) / (k + 1) + x * ((4 - 6 * σ) * ((k : ℝ) / (k + 1)))) := by
      positivity
    have p4 : 0 ≤ T ^ (x * ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) + 2 / (4 * (k : ℝ) + 3)) := by
      positivity
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left e1 hTε,
      mul_nonneg hQ p1, mul_nonneg hQ p2, mul_nonneg hQ p3, mul_nonneg hQ p4,
      mul_nonneg hTε p1, mul_nonneg hTε p2, mul_nonneg hTε p3, mul_nonneg hTε p4]

lemma trunc {T x σ δ : ℝ} {N : ℕ} (hT0 : 0 < T) (hTone : 1 ≤ T) (hy : (N : ℝ) = T ^ x)
    (hx1 : 5 / 6 ≤ x) (hx2 : x ≤ 1) (_hs1 : 7 / 10 ≤ σ) (hs2 : σ ≤ 1) (hδ : 0 < δ)
    {K k : ℕ} (hK1 : 1 ≤ K) (hKδ : 10 / δ ≤ K) (hKk : K ≤ k) :
    Fk T N σ K ≤ T ^ (δ / 2) * Fk T N σ k := by
  simp only [Fk, cN hT0 hy, cTT hT0]
  rw [mul_add, cTT hT0, cTT hT0]
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKkr : (K : ℝ) ≤ k := by exact_mod_cast hKk
  have hδK : 10 ≤ (K : ℝ) * δ := (div_le_iff₀ hδ).mp hKδ
  have hx0 : 0 ≤ x := by linarith
  have hxs : 0 ≤ x * (1 - σ) := mul_nonneg hx0 (by linarith)
  apply add_le_add <;> apply pmono hTone
  · have hu1 : 1 - δ / 2 ≤ (K : ℝ) / (K + 1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have huv : (K : ℝ) / (K + 1) ≤ (k : ℝ) / (k + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hv1 : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hd : -1 ≤ 1 + x * (4 - 6 * σ) := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ 1 + x * (4 - 6 * σ) + 1 by linarith) (sub_nonneg.2 huv)]
  · have hwδ : 5 * (1 / (4 * (K : ℝ) + 3)) ≤ δ / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    have hww : 1 / (4 * (k : ℝ) + 3) ≤ 1 / (4 * (K : ℝ) + 3) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hw0 : 0 ≤ 1 / (4 * (k : ℝ) + 3) := by positivity
    have hw : 4 * (K : ℝ) / (4 * K + 3) = 1 - 3 * (1 / (4 * K + 3)) := by field_simp; ring
    have hw' : 4 * (k : ℝ) / (4 * k + 3) = 1 - 3 * (1 / (4 * k + 3)) := by field_simp; ring
    have h2 : 2 / (4 * (K : ℝ) + 3) = 2 * (1 / (4 * K + 3)) := by ring
    have h2' : 2 / (4 * (k : ℝ) + 3) = 2 * (1 / (4 * k + 3)) := by ring
    rw [hw, hw', h2, h2']
    have he : -1 ≤ x * (5 - 6 * σ) := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ 3 + 3 * (x * (5 - 6 * σ)) by linarith) (sub_nonneg.2 hww)]

lemma uniform (δ : ℝ) (hδ : 0 < δ) : ∃ C T₀ : ℝ, 0 ≤ C ∧ 2 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T →
    ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 1 → ∀ R : ℕ, Large T N σ R → ∀ k : ℕ, 1 ≤ k →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        Fk T N σ k) := by
  have hε : 0 < δ / 2 := by positivity
  choose C T₀ hC hT₀ h using fun k => fixed_k k (δ / 2) hε
  set K : ℕ := ⌈10 / δ⌉₊ + 1 with hKdef
  set S := Finset.range (K + 1) with hS
  refine ⟨∑ j ∈ S, C j, max 2 (∑ j ∈ S, |T₀ j|), Finset.sum_nonneg (fun j _ => hC j),
    le_max_left _ _, ?_⟩
  intro T hT N hN σ hs1 hs2 R hL k hk
  have hTj : ∀ j ∈ S, T₀ j ≤ T := fun j hj =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (T₀ i)) hj).trans
      ((le_max_right _ _).trans hT))
  have hCj : ∀ j ∈ S, C j ≤ ∑ j ∈ S, C j := fun j hj =>
    Finset.single_le_sum (fun i _ => hC i) hj
  have hCt : 0 ≤ ∑ j ∈ S, C j := Finset.sum_nonneg (fun j _ => hC j)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  obtain ⟨x, hy, hx1, hx2, hN2⟩ := setup hT2 hN
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hδ2 : T ^ (δ / 2) ≤ T ^ δ := pmono hTone (by linarith)
  have hδ22 : T ^ (δ / 2) * T ^ (δ / 2) = T ^ δ := by rw [cTT hT0]; ring_nf
  have hA : 0 ≤ (N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) := by
    positivity
  have hF : ∀ j, 0 ≤ Fk T N σ j := fun j => by unfold Fk; positivity
  have hTd : 0 ≤ T ^ (δ / 2) := by positivity
  have hTδ : 0 ≤ T ^ δ := by positivity
  by_cases hkK : k ≤ K
  · have hkS : k ∈ S := Finset.mem_range.2 (by omega)
    have h1 := h k T (hTj k hkS) N hN σ hs1 hs2 R hL hk
    refine h1.trans ?_
    have := hF k
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul (hCj k hkS) hδ2 hTd hCt
  · have hKS : K ∈ S := Finset.mem_range.2 (by omega)
    have h1 := h K T (hTj K hKS) N hN σ hs1 hs2 R hL (by omega)
    have hKδ : 10 / δ ≤ (K : ℝ) := by
      rw [hKdef]; push_cast; linarith [Nat.le_ceil (10 / δ)]
    have htr := trunc hT0 hTone hy hx1 hx2 hs1 hs2 hδ (by omega : 1 ≤ K) hKδ
      (by omega : K ≤ k)
    have hCK := hCj K hKS
    have hCK0 := hC K
    have hFk := hF k
    refine h1.trans ?_
    set Ct := ∑ j ∈ S, C j
    set A := (N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ)
    have s1 : C K * T ^ (δ / 2) * (A + Fk T N σ K) ≤
        C K * T ^ (δ / 2) * (A + T ^ (δ / 2) * Fk T N σ k) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCK0 hTd)
    refine s1.trans ?_
    rw [show C K * T ^ (δ / 2) * (A + T ^ (δ / 2) * Fk T N σ k) =
      C K * T ^ (δ / 2) * A + C K * (T ^ (δ / 2) * T ^ (δ / 2)) * Fk T N σ k by ring, hδ22]
    have m1 := mul_le_mul hCK hδ2 hTd hCt
    nlinarith [mul_le_mul_of_nonneg_right m1 hA,
      mul_le_mul_of_nonneg_right hCK (mul_nonneg hTδ hFk)]

/-! ## Choosing `k` for the second display -/
lemma g_le {x σ M : ℝ} {k : ℕ} (h : (k : ℝ) * (1 + x * (4 - 6 * σ)) ≤ (k + 1) * M) :
    (k : ℝ) / (k + 1) + x * ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) ≤ M := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [show (k : ℝ) / (k + 1) + x * ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) =
    ((k : ℝ) * (1 + x * (4 - 6 * σ))) / (k + 1) by ring, div_le_iff₀ hk]
  linarith

lemma h_le {x σ M : ℝ} {k : ℕ} (h : 4 * (k : ℝ) * (x * (5 - 6 * σ)) + 2 ≤ (4 * k + 3) * M) :
    x * ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) + 2 / (4 * (k : ℝ) + 3) ≤ M := by
  have hk : (0 : ℝ) < 4 * k + 3 := by positivity
  rw [show x * ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) + 2 / (4 * (k : ℝ) + 3) =
    (4 * (k : ℝ) * (x * (5 - 6 * σ)) + 2) / (4 * k + 3) by ring, div_le_iff₀ hk]
  linarith

lemma nat_between (L : ℝ) : ∃ k : ℕ, 1 ≤ k ∧ L ≤ k ∧ (k : ℝ) ≤ max 1 (L + 1) := by
  refine ⟨max 1 ⌈L⌉₊, le_max_left _ _, ?_, ?_⟩
  · push_cast; exact (Nat.le_ceil L).trans (le_max_right _ _)
  · push_cast
    rcases le_or_gt 0 L with hL | hL
    · exact max_le_max le_rfl (Nat.ceil_lt_add_one hL).le
    · rw [Nat.ceil_eq_zero.2 hL.le]; simp

lemma ex_k {x σ : ℝ} (hx1 : 5 / 6 ≤ x) (hx2 : x ≤ 1) (hs1 : 7 / 10 ≤ σ) (hs2 : σ < 39 / 50) :
    1 + x * (1 - 2 * σ) ≤ 1 / 2 + x * (3 - 4 * σ) ∨ ∃ k : ℕ, 1 ≤ k ∧
      (k : ℝ) / (k + 1) + x * ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) ≤
        max ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) (x * (2 - 2 * σ)) ∧
      x * ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) + 2 / (4 * (k : ℝ) + 3) ≤
        max ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) (x * (2 - 2 * σ)) := by
  rcases eq_or_lt_of_le hx2 with hx | hx
  · subst hx
    by_cases hs : σ ≤ 3 / 4
    · left; linarith
    · right
      rw [not_le] at hs
      obtain ⟨k, hk1, hkL, -⟩ := nat_between ((6 * σ - 4) / (4 * (4 * σ - 3)))
      have hk0 : (0 : ℝ) ≤ k := by positivity
      refine ⟨k, hk1, (g_le ?_).trans (le_max_right _ _), (h_le ?_).trans (le_max_right _ _)⟩
      · nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ 4 * σ - 3 by linarith)]
      · have hp : 0 < 4 * (4 * σ - 3) := by linarith
        have := (div_le_iff₀ hp).mp hkL
        nlinarith
  · rcases eq_or_lt_of_le hs1 with hs | hs
    · right
      refine ⟨1, le_rfl, (g_le ?_).trans (le_max_left _ _), (h_le ?_).trans (le_max_left _ _)⟩
      · rw [← hs]; push_cast; nlinarith
      · rw [← hs]; push_cast; nlinarith
    · right
      have hp : 0 < 10 * σ - 7 := by linarith
      have hq : 0 < 13 - 15 * σ := by linarith
      have hm : 0 < 1 - x := by linarith
      set τ := (30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5) with hτ
      have hte : τ - x * (5 - 6 * σ) = 3 * (10 * σ - 7) * (1 - x) / 5 := by rw [hτ]; ring
      have hdt : 1 + x * (4 - 6 * σ) - τ = 2 * (13 - 15 * σ) * (1 - x) / 5 := by rw [hτ]; ring
      have hte0 : 0 < τ - x * (5 - 6 * σ) := by rw [hte]; positivity
      have hdt0 : 0 < 1 + x * (4 - 6 * σ) - τ := by rw [hdt]; positivity
      have h4 : 0 < 4 * (τ - x * (5 - 6 * σ)) := by linarith
      set L := (2 - 3 * τ) / (4 * (τ - x * (5 - 6 * σ))) with hL
      have hL4 : L * (4 * (τ - x * (5 - 6 * σ))) = 2 - 3 * τ := div_mul_cancel₀ _ h4.ne'
      obtain ⟨k, hk1, hkL, hkU⟩ := nat_between L
      have hU1 : 1 + x * (4 - 6 * σ) - τ ≤ τ := by
        rw [hτ]
        nlinarith [mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hs1),
          mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hs1)]
      have hquad : 0 ≤ -90 * σ ^ 2 + 123 * σ - 41 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hs1) (show (0 : ℝ) ≤ 39 / 50 - σ by linarith)]
      have hcubic : (2 - 3 * τ) * (1 + x * (4 - 6 * σ) - τ) +
          4 * (τ - x * (5 - 6 * σ)) * (1 + x * (4 - 6 * σ) - τ) ≤
          4 * (τ - x * (5 - 6 * σ)) * τ := by
        have hid : 4 * (τ - x * (5 - 6 * σ)) * τ - ((2 - 3 * τ) * (1 + x * (4 - 6 * σ) - τ) +
            4 * (τ - x * (5 - 6 * σ)) * (1 + x * (4 - 6 * σ) - τ)) =
            (2 * (1 - x) / 25) * (5 * (6 * x - 5) * (-90 * σ ^ 2 + 123 * σ - 41)) := by
          rw [hτ]; ring
        have : 0 ≤ (2 * (1 - x) / 25) * (5 * (6 * x - 5) * (-90 * σ ^ 2 + 123 * σ - 41)) := by
          apply mul_nonneg (by positivity)
          exact mul_nonneg (by linarith) hquad
        linarith
      have hLU : (L + 1) * (1 + x * (4 - 6 * σ) - τ) ≤ τ := by
        refine le_of_mul_le_mul_left ?_ h4
        have : 4 * (τ - x * (5 - 6 * σ)) * ((L + 1) * (1 + x * (4 - 6 * σ) - τ)) =
            L * (4 * (τ - x * (5 - 6 * σ))) * (1 + x * (4 - 6 * σ) - τ) +
            4 * (τ - x * (5 - 6 * σ)) * (1 + x * (4 - 6 * σ) - τ) := by ring
        rw [this, hL4]; linarith
      have hkd : (k : ℝ) * (1 + x * (4 - 6 * σ) - τ) ≤ τ := by
        rcases le_max_iff.mp hkU with h | h
        · nlinarith
        · nlinarith
      refine ⟨k, hk1, (g_le ?_).trans (le_max_left _ _), (h_le ?_).trans (le_max_left _ _)⟩
      · nlinarith
      · nlinarith [mul_le_mul_of_nonneg_right hkL h4.le]

lemma second (δ : ℝ) (hδ : 0 < δ) : ∃ C T₀ : ℝ, 0 ≤ C ∧ 2 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T →
    ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 1 → ∀ R : ℕ, Large T N σ R →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by
  obtain ⟨CU, TU, hCU, hTU, hU⟩ := uniform δ hδ
  obtain ⟨CJ, hCJ, hJ⟩ := large_jutila δ hδ
  obtain ⟨Tc, hTc, hcl⟩ := large_classical δ hδ
  refine ⟨3 * CU + 2 * CJ + 2, max (max TU Tc) 2, by positivity, le_max_right _ _, ?_⟩
  intro T hT N hN σ hs1 hs2 R hL
  have hT1 : TU ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : Tc ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT2' : 2 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨x, hy, hx1, hx2, hN2⟩ := setup hT2' hN
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hTδ : 0 ≤ T ^ δ := by positivity
  have hQU : 0 ≤ CU * T ^ δ := by positivity
  have hQJ : 0 ≤ CJ * T ^ δ := by positivity
  simp only [cN hT0 hy, cTT hT0]
  have p1 : 0 ≤ T ^ (x * (2 - 2 * σ)) := by positivity
  have p2 : 0 ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := by positivity
  have p3 : 0 ≤ T ^ ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) := by positivity
  by_cases hs : 39 / 50 ≤ σ
  · have h := hJ T hT2' N (by omega) σ R hL
    simp only [cN hT0 hy, cT1 hT0] at h
    have e1 : T ^ (1 + x * ((10 - 16 * σ) / 3)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) :=
      pmono hTone (by nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hs1)])
    have e2 : T ^ (1 + x * (18 - 24 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) :=
      pmono hTone (by nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hs)])
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left e1 hQJ, mul_le_mul_of_nonneg_left e2 hQJ,
      mul_nonneg hQJ p1, mul_nonneg hQJ p2, mul_nonneg hQJ p3,
      mul_nonneg hQU p1, mul_nonneg hQU p2, mul_nonneg hQU p3,
      mul_nonneg hTδ p1, mul_nonneg hTδ p2, mul_nonneg hTδ p3]
  · rw [not_le] at hs
    rcases ex_k hx1 hx2 hs1 hs with hc | ⟨k, hk, hg, hh⟩
    · have h := (hcl T hT2 N (by omega) σ R hL).1
      simp only [cN hT0 hy, cT1 hT0] at h
      have e1 : T ^ (1 + x * (1 - 2 * σ)) ≤ T ^ (1 / 2 + x * (3 - 4 * σ)) := pmono hTone hc
      refine h.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left e1 hTδ,
        mul_nonneg hQJ p1, mul_nonneg hQJ p2, mul_nonneg hQJ p3,
        mul_nonneg hQU p1, mul_nonneg hQU p2, mul_nonneg hQU p3,
        mul_nonneg hTδ p1, mul_nonneg hTδ p2, mul_nonneg hTδ p3]
    · have h := hU T hT1 N hN σ hs1 hs2 R hL k hk
      simp only [Fk, cN hT0 hy, cTT hT0] at h
      have hmax : T ^ (max ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) (x * (2 - 2 * σ))) ≤
          T ^ ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) + T ^ (x * (2 - 2 * σ)) := by
        rcases max_choice ((30 * σ - 21) / 5 + x * ((46 - 60 * σ) / 5)) (x * (2 - 2 * σ))
          with h' | h' <;> rw [h'] <;> linarith
      have e1 := (pmono hTone hg).trans hmax
      have e2 := (pmono hTone hh).trans hmax
      refine h.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left e1 hQU, mul_le_mul_of_nonneg_left e2 hQU,
        mul_nonneg hQJ p1, mul_nonneg hQJ p2, mul_nonneg hQJ p3,
        mul_nonneg hQU p1, mul_nonneg hQU p2, mul_nonneg hQU p3,
        mul_nonneg hTδ p1, mul_nonneg hTδ p2, mul_nonneg hTδ p3]

/-! ## The target -/
theorem card_le_of_large_values_of_five_sixths_dev :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, 7 / 10 ≤ σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        ⨅ k : ℕ+, (T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
          (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)))) ∧
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by
  intro δ hδ
  obtain ⟨C1, T1, hC1, hT1, h1⟩ := uniform δ hδ
  obtain ⟨C2, T2, hC2, hT2, h2⟩ := second δ hδ
  refine ⟨max (max C1 C2) 1, max T1 T2, ?_⟩
  intro T hT N hN σ hs1 b hb R t hsep ht hl
  have hL : Large T N σ R := ⟨b, t, hb, hsep, ht, hl⟩
  have hTa : T1 ≤ T := (le_max_left _ _).trans hT
  have hTb : T2 ≤ T := (le_max_right _ _).trans hT
  have hT2' : 2 ≤ T := hT1.trans hTa
  obtain ⟨x, hy, hx1, hx2, hN2⟩ := setup hT2' hN
  have hT0 : 0 < T := by linarith
  set C := max (max C1 C2) 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM : 0 < C * T ^ δ := by positivity
  set I := ⨅ k : ℕ+, (T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
          (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)))
    with hI
  have hI0 : 0 ≤ I := le_ciInf (fun k => by positivity)
  set A := (N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hτ0 : 0 ≤ T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5) := by positivity
  by_cases hs2 : σ ≤ 1
  · constructor
    · have key : ∀ k : ℕ+, (R : ℝ) / (C * T ^ δ) - A ≤ Fk T N σ k := by
        intro k
        have h := h1 T hTa N hN σ hs1 hs2 R hL k k.pos
        have hFk : 0 ≤ Fk T N σ k := by unfold Fk; positivity
        have h' : (R : ℝ) ≤ (A + Fk T N σ k) * (C * T ^ δ) := by
          refine h.trans ?_
          rw [mul_comm (A + _)]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)) (by linarith)
        have := (div_le_iff₀ hM).2 h'
        linarith
      have hinf : (R : ℝ) / (C * T ^ δ) - A ≤ I := le_ciInf key
      have : (R : ℝ) / (C * T ^ δ) ≤ A + I := by linarith
      rw [div_le_iff₀ hM] at this
      linarith
    · refine (h2 T hTb N hN σ hs1 hs2 R hL).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)) (by linarith)
  · have hR := large_zero hN2 (lt_of_not_ge hs2) hL
    subst hR
    simp only [CharP.cast_eq_zero]
    exact ⟨mul_nonneg hM.le (by linarith), mul_nonneg hM.le (by linarith)⟩

end GuthMaynardS1213.P121.PartB
end

section
namespace GuthMaynardS1213.P121
open GuthMaynard
alias card_le_of_large_values_of_five_sixths_dev := GuthMaynardS1213.P121.PartB.card_le_of_large_values_of_five_sixths_dev

end GuthMaynardS1213.P121
end

open GuthMaynard in
theorem solution :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, 7 / 10 ≤ σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        ⨅ k : ℕ+, (T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
          (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)))) ∧
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) :=
  GuthMaynardS1213.P121.card_le_of_large_values_of_five_sixths_dev
