-- Prove2me | solution 1 for OAI.Erdos3.uniformBlockSpectrum_tail_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:42.511979+00:00
-- url     : https://prove2.me/submissions/add6e578-945a-4dae-a2da-cbd353fb3f75

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B080
import Definitions.Def_OAIE3v2B086

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spectrumTail_le_card {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) : spectrumTail S f ≤ Fintype.card K * w := by
  calc
    _ ≤ ∑ _k : K, w := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false]
      · exact hw
      · exact h k hk
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem spectrumTail_step {K : Type*} [Fintype K] [DecidableEq K]
    (S T : Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) :
    spectrumTail S f ≤ T.card * w + spectrumTail T f := by
  have hp (k : K) : (if k ∈ S then 0 else f k) ≤
      (if k ∈ T then w else 0) + (if k ∈ T then 0 else f k) := by
    by_cases hs : k ∈ S <;> by_cases ht : k ∈ T <;>
      simp only [hs, ht, ite_true, ite_false, zero_add, add_zero]
    · exact hw
    · exact hf k
    · exact h k hs
    · exact le_rfl
  calc
    _ ≤ ∑ k, ((if k ∈ T then w else 0) + (if k ∈ T then 0 else f k)) :=
      Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, spectrumTail]

theorem spectrumTail_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i k, k ∉ S i → f k ≤ w i) (n : ℕ) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  induction n generalizing S w with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, zero_add] using
      spectrumTail_le_card (S 0) f (hw 0) (h 0)
  | succ n ih =>
      have hstep := spectrumTail_step (S 0) (S 1) f hf (hw 0) (h 0)
      have htail := ih (fun i => S (i + 1)) (fun i => w (i + 1))
        (fun i => hw (i + 1)) (fun i => h (i + 1))
      calc
        _ ≤ (S 1).card * w 0 + ((∑ i ∈ Finset.range n, (S (i + 1 + 1)).card * w (i + 1)) +
            Fintype.card K * w (n + 1)) := hstep.trans (add_le_add le_rfl htail)
        _ = _ := by rw [Finset.sum_range_succ']; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spectrumTail_finite_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  have hs := spectrumTail_levels (fun i => S (min i n)) f hf (fun i => w (min i n))
    (fun i => hw _ (Nat.min_le_right i n)) (fun i => h _ (Nat.min_le_right i n)) n
  simp only [Nat.zero_min, Nat.min_self] at hs
  have heq : (∑ i ∈ Finset.range n, (S (min (i + 1) n)).card * w (min i n)) =
      ∑ i ∈ Finset.range n, (S (i + 1)).card * w i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.min_eq_left (by omega : i + 1 ≤ n), Nat.min_eq_left (by omega : i ≤ n)]
  rwa [heq] at hs

theorem spectrumTail_finite_geometric {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * w i ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) f ≤ 2 * C + Fintype.card K * w n := by
  apply (spectrumTail_finite_levels S f hf w n hw h).trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ i ∈ Finset.range n, C * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i hi => hlevel i (Finset.mem_range.mp hi))
    _ = C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hC
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IndependentPhaseCoefficients
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem norm_product_coefficients_le {B : Type*} [Fintype B] (c : B → ℂ) {ζ : ℝ}
    (h : ∀ b, ‖c b‖ ≤ ζ) : ‖∏ b, c b‖ ≤ ζ ^ Fintype.card B := by
  classical
  rw [norm_prod]
  calc
    _ ≤ ∏ _b : B, ζ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun index _ => h index)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialSpectrumAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem product_spectrumTail_geometric {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (ζ : ℕ → ℝ) (n : ℕ)
    (hζ : ∀ i ≤ n, 0 ≤ ζ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * (ζ i) ^ Fintype.card B ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * C + Fintype.card K * (ζ n) ^ Fintype.card B := by
  apply spectrumTail_finite_geometric S _ (fun _ => norm_nonneg _) _ n
    (fun i hi => pow_nonneg (hζ i hi) _) _ hC hlevel
  intro i hi k hk
  exact norm_product_coefficients_le _ (fun b => hsmall i hi b k hk)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem dyadic_power_ratio {a b : ℕ} (hab : a + 1 ≤ b) (i : ℕ) :
    (2 : ℝ) ^ (a * i) / 2 ^ (b * i) ≤ (1 / 2 : ℝ) ^ i := by
  rw [one_div_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right i hab

theorem dyadic_level_mass_bound {a b i : ℕ} {C ζ count : ℝ}
    (hab : a + 1 ≤ b) (hC : 0 ≤ C) (hζ : 0 ≤ ζ)
    (hcount : count ≤ C * ((2 : ℝ) ^ a) ^ i) :
    count * (ζ / 2 ^ i) ^ b ≤ (C * ζ ^ b) * (1 / 2 : ℝ) ^ i := by
  calc
    _ ≤ (C * ((2 : ℝ) ^ a) ^ i) * (ζ / 2 ^ i) ^ b :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C * ζ ^ b) * ((2 : ℝ) ^ (a * i) / 2 ^ (b * i)) := by
      rw [div_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm i b]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_power_ratio hab i) (by positivity)

theorem product_spectrumTail_dyadic {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a : ℕ) {C ζ : ℝ}
    (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hab : a + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ C * ((2 : ℝ) ^ a) ^ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * (C * ζ ^ Fintype.card B) + Fintype.card K * (ζ / 2 ^ n) ^ Fintype.card B := by
  apply product_spectrumTail_geometric c S (fun i => ζ / 2 ^ i) n
    (fun _ _ => by positivity) hsmall (by positivity)
  intro i hi
  exact dyadic_level_mass_bound hab hC hζ (hcount i hi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem cutoff_power_mass_bound {N T δ ζ : ℝ} {p b : ℕ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hδζ : δ ≤ ζ) (hpb : p ≤ b)
    (hcutoff : N * δ ^ p ≤ T) : N * δ ^ b ≤ T * ζ ^ (b - p) := by
  have he : δ ^ b = δ ^ p * δ ^ (b - p) := by
    rw [← pow_add, Nat.add_sub_of_le hpb]
  rw [he, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hcutoff (pow_nonneg hδ _)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hδζ _) hT)

theorem dyadic_polynomial_count_factor (A ζ : ℝ) (a i : ℕ) :
    A * ((2 : ℝ) ^ (i + 1) / ζ) ^ a = (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
  simp only [pow_succ', mul_pow, div_pow, ← pow_mul]
  rw [Nat.mul_comm i a]
  ring

theorem polynomial_bias_mass_factor {A ζ : ℝ} {a b : ℕ}
    (hζ : 0 < ζ) (hab : a ≤ b) :
    (A * (2 / ζ) ^ a) * ζ ^ b = A * 2 ^ a * ζ ^ (b - a) := by
  rw [div_pow, pow_sub₀ ζ hζ.ne' hab]
  ring

theorem product_spectrumTail_polynomial_cutoff {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * A * 2 ^ a * ζ ^ (Fintype.card B - a) + T * ζ ^ (Fintype.card B - p) := by
  have hc : ∀ i < n, ((S (i + 1)).card : ℝ) ≤
      (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
    intro i hi
    rw [← dyadic_polynomial_count_factor]
    exact hcount i hi
  have ht := product_spectrumTail_dyadic c S n a (by positivity) hζ.le hab hc hsmall
  rw [polynomial_bias_mass_factor hζ (by omega)] at ht
  have hδ : ζ / 2 ^ n ≤ ζ := by
    exact div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hb := cutoff_power_mass_bound hT (by positivity) hδ hpb hcutoff
  exact ht.trans (by nlinarith only [hb])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem product_spectrumTail_le_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ ε : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T)
    (haccuracy : (2 * A * 2 ^ a + T) * ζ ≤ ε) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤ ε := by
  have ht := product_spectrumTail_polynomial_cutoff c S n a p hA hT hζ hab (by omega)
    hcount hsmall hcutoff
  have ha : ζ ^ (Fintype.card B - a) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  have hp : ζ ^ (Fintype.card B - p) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  apply ht.trans
  calc
    _ ≤ 2 * A * 2 ^ a * ζ + T * ζ := by gcongr
    _ = (2 * A * 2 ^ a + T) * ζ := by ring
    _ ≤ ε := haccuracy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

theorem exists_length_dyadic_cutoff {C L ζ : ℝ} {c : ℕ}
    (hC : 0 < C) (hζ : 0 < ζ) (hc : 0 < c) (hstart : C / ζ ^ c ≤ L) :
    ∃ n : ℕ, (∀ i ≤ n, C / (ζ / 2 ^ i) ^ c ≤ L) ∧
      L * (ζ / 2 ^ n) ^ c ≤ 2 ^ c * C := by
  have hpow : 0 < ζ ^ c := pow_pos hζ _
  have hstart' : C ≤ L * ζ ^ c := (div_le_iff₀ hpow).mp hstart
  have hx : 1 ≤ L * ζ ^ c / C := (le_div_iff₀ hC).mpr (by simpa)
  have hy : (1 : ℝ) < 2 ^ c := one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hy
  have hswitch (i : ℕ) : ((2 : ℝ) ^ c) ^ i = (2 ^ i) ^ c := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm c i]
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hi' : ((2 : ℝ) ^ c) ^ i ≤ L * ζ ^ c / C :=
      (pow_le_pow_right₀ hy.le hi).trans hn
    have hi'' : C * (2 ^ i) ^ c ≤ L * ζ ^ c := by
      have hh := (le_div_iff₀ hC).mp hi'
      rw [hswitch] at hh
      linarith only [hh]
    rw [div_pow]
    apply (div_le_iff₀ (div_pos hpow (by positivity))).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 ^ i) ^ c)).mpr
    exact hi''
  · have hh := (div_lt_iff₀ hC).mp hn'
    rw [pow_succ, hswitch] at hh
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ n) ^ c)).mpr
    nlinarith only [hh]

theorem length_cutoff_mass_bound {N V L C δ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsize : N ≤ V * L ^ t) (hcutoff : L * δ ^ c ≤ C) :
    N * δ ^ (c * t) ≤ V * C ^ t := by
  calc
    _ ≤ (V * L ^ t) * δ ^ (c * t) :=
      mul_le_mul_of_nonneg_right hsize (pow_nonneg hδ _)
    _ = V * (L * δ ^ c) ^ t := by rw [mul_pow, pow_mul]; ring
    _ ≤ V * C ^ t := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hL (pow_nonneg hδ _)) hcutoff t) hV

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

theorem frequencyGridInterval_card (M : ℕ) (center : ℝ) {radius : ℝ} (hr : 0 ≤ radius) :
    ((frequencyGridInterval M center radius).card : ℝ) ≤ 2 * radius + 1 := by
  classical
  let A := frequencyGridInterval M center radius
  have hinj : Function.Injective (fun k : Fin M => (k.val : ℤ)) := by
    intro x y h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hc := card_integer_set_le_diameter_add_one (A.image (fun k => (k.val : ℤ)))
    (by positivity : (0 : ℝ) ≤ 2 * radius) (by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hi' := abs_le.mp (Finset.mem_filter.mp hi).2
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      push_cast
      rw [abs_le]
      constructor <;> linarith)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalGridMajorSet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerSymmetricInterval_card (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  omega

theorem rationalGridMajorSet_card (M Q H : ℕ) :
    ((rationalGridMajorSet M Q H).card : ℝ) ≤
      (Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
  classical
  let A := Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)
  have hA : (A.card : ℝ) = 2 * Q * (H + 1) + 1 := by
    have h := integerSymmetricInterval_card (Q * (H + 1))
    dsimp only [A]
    norm_cast at h ⊢
    simpa only [Nat.mul_assoc] using h
  have hd (d : ℕ) :
      ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) ≤
        (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
    calc
      _ ≤ ∑ a ∈ A, ((frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ A, (2 * (H : ℝ) + 1) :=
        Finset.sum_le_sum (fun a _ => frequencyGridInterval_card M _ (Nat.cast_nonneg H))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hA]
  unfold rationalGridMajorSet
  calc
    _ ≤ ∑ d ∈ Finset.range (Q + 1),
        ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ Finset.range (Q + 1), ((2 * (Q : ℝ) * (H + 1) + 1) * (2 * H + 1)) :=
      Finset.sum_le_sum (fun d _ => hd d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

theorem rationalGridMajorBox_card (J : Type*) [Fintype J] [DecidableEq J] (M Q H : ℕ) :
    ((rationalGridMajorBox J M Q H).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ Fintype.card J := by
  classical
  unfold rationalGridMajorBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (rationalGridMajorSet_card M Q H) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

theorem one_le_inverse_power {C ζ : ℝ} (hC : 1 ≤ C) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (r : ℕ) : 1 ≤ C / ζ ^ r := by
  apply (le_div_iff₀ (pow_pos hζ r)).mpr
  simpa only [one_mul] using (pow_le_one₀ hζ.le hζ1 : ζ ^ r ≤ 1).trans hC

theorem rationalGridMajorBox_ceil_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((rationalGridMajorBox J M ⌈X⌉₊ ⌈X⌉₊).card : ℝ) ≤
      (195 * X ^ 4) ^ Fintype.card J := by
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : (0 : ℝ) ≤ ⌈X⌉₊ := Nat.cast_nonneg _
  have hQ : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one hX0
    linarith
  have hQ1 : (⌈X⌉₊ : ℝ) + 1 ≤ 3 * X := by linarith
  have hp := mul_le_mul hQ hQ1 (by positivity : 0 ≤ (⌈X⌉₊ : ℝ) + 1) (by positivity)
  have hm : 2 * (⌈X⌉₊ : ℝ) * (⌈X⌉₊ + 1) + 1 ≤ 13 * X ^ 2 := by
    nlinarith [sq_nonneg (X - 1)]
  have hr : 2 * (⌈X⌉₊ : ℝ) + 1 ≤ 5 * X := by linarith
  have hbase : ((⌈X⌉₊ : ℝ) + 1) * (2 * ⌈X⌉₊ * (⌈X⌉₊ + 1) + 1) *
      (2 * ⌈X⌉₊ + 1) ≤ 195 * X ^ 4 := by
    calc
      _ ≤ (3 * X) * (13 * X ^ 2) * (5 * X) := by gcongr
      _ = _ := by ring
  exact (rationalGridMajorBox_card J M ⌈X⌉₊ ⌈X⌉₊).trans
    (pow_le_pow_left₀ (by positivity) hbase _)

theorem polynomialGridCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {C ζ : ℝ} (r : ℕ) (hC : 1 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M C r ζ).card : ℝ) ≤
      (195 * C ^ 4) ^ Fintype.card J / ζ ^ (4 * r * Fintype.card J) := by
  have h := rationalGridMajorBox_ceil_card J M (one_le_inverse_power hC hζ hζ1 r)
  unfold polynomialGridCover
  apply h.trans_eq
  simp only [div_pow, ← mul_div_assoc, ← pow_mul]
  rw [Nat.mul_comm r 4]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem lengthAwareSpectrumCover_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (coeff : B → K → ℂ) (cover : ℝ → Finset K) {C L V A ζ ε : ℝ} {c t a : ℕ}
    (hC : 0 < C) (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hc : 0 < c)
    (haB : a + 1 ≤ Fintype.card B) (htB : c * t + 1 ≤ Fintype.card B)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ∀ δ, 0 < δ → δ ≤ 1 → ((cover δ).card : ℝ) ≤ A / δ ^ a)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → C / δ ^ c ≤ L →
      ∀ b k, k ∉ cover δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : (2 * A * 2 ^ a + V * (2 ^ c * C) ^ t) * ζ ≤ ε) :
    spectrumTail (lengthAwareSpectrumCover C L c cover ζ)
      (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · obtain ⟨n, hn, hlast⟩ := exists_length_dyadic_cutoff hC hζ hc hstart
    have hδ (i : ℕ) : 0 < ζ / 2 ^ i ∧ ζ / 2 ^ i ≤ 1 := by
      refine ⟨by positivity, ?_⟩
      exact (div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hζ1
    have hb := length_cutoff_mass_bound hV hL (hδ n).1.le hsize hlast
    have hcount (i : ℕ) (_hi : i < n) :
        ((cover (ζ / 2 ^ (i + 1))).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a := by
      have hh := hcover (ζ / 2 ^ (i + 1)) (hδ _).1 (hδ _).2
      apply hh.trans_eq
      simp only [div_pow, div_div_eq_mul_div]
      ring
    have hsmall (i : ℕ) (hi : i ≤ n) :=
      hminor (ζ / 2 ^ i) (hδ i).1 (hδ i).2 (hn i hi)
    have ht := product_spectrumTail_le_accuracy coeff (fun i => cover (ζ / 2 ^ i))
      n a (c * t) hA (by positivity) hζ hζ1 haB htB hcount hsmall hb haccuracy
    simpa only [lengthAwareSpectrumCover, if_pos hstart, pow_zero, div_one] using ht
  · simpa only [lengthAwareSpectrumCover, if_neg hstart, spectrumTail,
      Finset.mem_univ, ite_true, Finset.sum_const_zero] using hε

end Erdos3

end

section

namespace Erdos3

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

end Erdos3

end

section

namespace Erdos3

theorem majorArcBiasConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcBiasConstant n U := by
  have h := localizedMajorArcBudget_pos n hU (by norm_num : (0 : ℝ) < 1)
  rw [localizedMajorArcBudget_eq_power n hU (by norm_num)] at h
  simpa only [majorArcBiasConstant, majorArcBiasExponent, one_pow, div_one] using h

theorem majorArcLocalizationConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLocalizationConstant n U := by
  have : 0 < U := lt_of_lt_of_le (by norm_num) hU
  unfold majorArcLocalizationConstant
  positivity

theorem majorArcLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLengthConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcLengthConstant
  positivity

theorem majorArcErrorConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcErrorConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3

theorem majorArcCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ majorArcCoverConstant n j U V := by
  have hq := (majorArcBiasConstant_pos n hU).le
  have he := (majorArcErrorConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  unfold majorArcCoverConstant
  nlinarith only [hd, mul_nonneg hV he]

theorem majorArcSpectrumConstant_nonneg (n j : ℕ) (U V : ℝ) :
    0 ≤ majorArcSpectrumConstant n j U V := by
  unfold majorArcSpectrumConstant
  positivity

theorem uniformMajorArcCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) {U V ζ : ℝ} (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J)) ζ).card : ℝ) ≤
      majorArcSpectrumConstant n (Fintype.card J) U V /
        ζ ^ majorArcSpectrumExponent n (Fintype.card J) :=
  polynomialGridCover_card J M _ (majorArcCoverConstant_one_le n _ hU hV) hζ hζ1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniformBlockSpectrum_tail_s2_oai {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : uniformBlockSpectrumAccuracyConstant n (Fintype.card J) t U V W * ζ ≤ ε) :
    spectrumTail (uniformBlockSpectrumCover J M n U V L ζ) (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  classical
  apply lengthAwareSpectrumCover_accuracy coeff _ (t := t)
    (a := majorArcSpectrumExponent n (Fintype.card J))
    (majorArcLengthConstant_pos n hU) hL hW
    (majorArcSpectrumConstant_nonneg n (Fintype.card J) U V) hζ hζ1 hε
  · unfold majorArcLengthExponent; omega
  · unfold uniformSpectrumBlockCount at hB; omega
  · unfold uniformSpectrumBlockCount at hB; omega
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · intro δ hδ hδ1
    exact uniformMajorArcCover_card J M n hU hV hδ hδ1
  · exact hminor
  · exact haccuracy

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.uniformBlockSpectrum_tail_s2_oai.{u_1, u_2} := @OAI.Erdos3.uniformBlockSpectrum_tail_s2_oai.{u_1, u_2}
