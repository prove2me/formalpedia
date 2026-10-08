-- Prove2me | solution 1 for KarpPapadimitriou.Generator.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:22:19.740141+00:00
-- url     : https://prove2.me/submissions/aeca529d-e809-4584-9429-5e76277109af

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes



namespace KarpPapadimitriou.Generator

lemma normalLength_le (n P : ℕ) (f : Fin n → ℤ) (g : ℤ) (h : SmallHyperplane P f g) :
    0 < normalLength f ∧ normalLength f ≤ 2 ^ (n + P) := by
  obtain ⟨hf, hb, _⟩ := h
  constructor
  · unfold normalLength
    apply Real.sqrt_pos.mpr
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hf (funext hc)
    calc (0:ℝ) < (f i : ℝ)^2 := by positivity
      _ ≤ _ := Finset.single_le_sum (f := fun i => ((f i : ℝ)^2)) (fun j _ => by positivity) (Finset.mem_univ i)
  · unfold normalLength
    rw [show ((2:ℝ) ^ (n + P)) = Real.sqrt (((2:ℝ)^(n+P))^2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : ∀ i, ((f i : ℝ))^2 ≤ ((2:ℝ)^P)^2 := by
      intro i
      have h1 : |(f i : ℝ)| ≤ 2^P := by
        have := hb i
        have : ((f i).natAbs : ℝ) ≤ 2^P := by exact_mod_cast this
        simpa [Nat.cast_natAbs] using this
      calc ((f i : ℝ))^2 = |(f i : ℝ)|^2 := (sq_abs _).symm
        _ ≤ ((2:ℝ)^P)^2 := by gcongr
    calc ∑ i : Fin n, ((f i : ℝ) ^ 2) ≤ ∑ i : Fin n, ((2:ℝ)^P)^2 := Finset.sum_le_sum (fun i _ => this i)
      _ = n * ((2:ℝ)^P)^2 := by simp
      _ ≤ (2:ℝ)^n * ((2:ℝ)^P)^2 := by
          gcongr
          exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ ((2:ℝ)^(n+P))^2 := by
          rw [pow_add, mul_pow]
          have : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
          have h0 : (0:ℝ) ≤ ((2:ℝ)^P)^2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)^n ≤ (2^n)^2 by nlinarith) h0]

lemma tParam_ge (n P : ℕ) (c : Fin n → ℤ) (k : ℤ) : n + P ≤ tParam n P c k := by
  unfold tParam
  have h1 : n+1 ≤ (n+1)^2 := by nlinarith
  have h2 : (n+1)*(P+1) ≤ (n+1)^2*(P+1) := Nat.mul_le_mul_right _ h1
  have : n + P ≤ (n+1)^2*(P+1) := by nlinarith
  omega

theorem lemma4_core (n P : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (r : Fin n → ℚ) (f : Fin n → ℤ) (g : ℤ)
    (hsmall : SmallHyperplane P f g)
    (hden : ∀ i, (r i).den ≤ 2 ^ tParam n P c k)
    (hout : dotQ f r ≠ (g : ℚ)) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤
      hyperplaneDistance f g (realPoint r) := by
  set T := tParam n P c k with hT
  have hTge : n + P ≤ T := tParam_ge n P c k
  obtain ⟨hNpos, hNle⟩ := normalLength_le n P f g hsmall
  set D : ℕ := ∏ i, (r i).den with hD
  have hDle : D ≤ 2 ^ (T * n) := by
    calc D ≤ ∏ _i : Fin n, 2 ^ T := Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hden i)
      _ = 2 ^ (T * n) := by simp [pow_mul]
  have hDpos : 0 < D := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hint : ∀ i, ∃ z : ℤ, (D : ℚ) * r i = z := by
    intro i
    obtain ⟨e, he⟩ : (r i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(e : ℤ) * (r i).num, ?_⟩
    have h1 : (r i) * (r i).den = (r i).num := Rat.mul_den_eq_num (r i)
    rw [he]; push_cast
    rw [← h1]; ring
  choose z hz using hint
  have hK : (D : ℚ) * (dotQ f r - g) = ((∑ i, f i * z i - D * g : ℤ) : ℚ) := by
    unfold dotQ
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hz i]; ring
  have hKne : (∑ i, f i * z i - D * g : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at hK
    simp at hK
    rcases hK with h | h
    · exact absurd (by exact_mod_cast h : D = 0) hDpos.ne'
    · exact hout (by linarith)
  have hK1 : (1:ℝ) ≤ |(D:ℝ) * (((dotQ f r : ℚ) : ℝ) - g)| := by
    have : ((D : ℚ) * (dotQ f r - g) : ℚ) = ((∑ i, f i * z i - D * g : ℤ) : ℚ) := hK
    have h2 : (((D : ℚ) * (dotQ f r - g) : ℚ) : ℝ) = (((∑ i, f i * z i - D * g : ℤ) : ℚ) : ℝ) := by rw [this]
    push_cast at h2
    rw [h2]
    have : (1:ℤ) ≤ |(∑ i, f i * z i - D * g : ℤ)| := Int.one_le_abs hKne
    exact_mod_cast this
  have hdot : dotR f (realPoint r) = ((dotQ f r : ℚ) : ℝ) := by
    unfold dotR dotQ realPoint; push_cast; rfl
  unfold hyperplaneDistance
  rw [hdot]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ D)] at hK1
  have hDle' : (D:ℝ) ≤ 2 ^ (T * n) := by exact_mod_cast hDle
  have hA : (1:ℝ) / 2^(T*n) ≤ |((dotQ f r : ℚ) : ℝ) - g| := by
    rw [div_le_iff₀ (by positivity)]
    calc (1:ℝ) ≤ D * |((dotQ f r : ℚ) : ℝ) - g| := hK1
      _ ≤ 2^(T*n) * |((dotQ f r : ℚ) : ℝ) - g| := by gcongr
      _ = _ := by ring
  have hNle' : normalLength f ≤ 2 ^ T := le_trans hNle (pow_le_pow_right₀ (by norm_num) hTge)
  rw [le_div_iff₀ hNpos]
  have h3 : (1:ℝ) / 2 ^ ((n + 1) * T) * normalLength f ≤ 1 / 2^(T*n) := by
    rw [show (n+1)*T = T*n + T by ring, pow_add]
    calc (1:ℝ) / (2^(T*n) * 2^T) * normalLength f ≤ 1 / (2^(T*n) * 2^T) * 2^T := by gcongr
      _ = 1 / 2^(T*n) := by field_simp
  linarith

end KarpPapadimitriou.Generator

open KarpPapadimitriou.Generator


theorem solution (n P : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (r : Fin n → ℚ) (f : Fin n → ℤ) (g : ℤ)
    (hsmall : SmallHyperplane P f g)
    (hden : ∀ i, (r i).den ≤ 2 ^ tParam n P c k)
    (hout : dotQ f r ≠ (g : ℚ)) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤
      hyperplaneDistance f g (realPoint r) := by
  exact lemma4_core n P c k r f g hsmall hden hout
