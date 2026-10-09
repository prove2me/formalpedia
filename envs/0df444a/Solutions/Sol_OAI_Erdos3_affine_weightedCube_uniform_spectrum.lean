-- Prove2me | solution 1 for OAI.Erdos3.affine_weightedCube_uniform_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T13:29:12.97852+00:00
-- url     : https://prove2.me/submissions/381241b1-6a18-4554-a281-9d998584ee7e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088
import Theorems.Thm_OAI_Erdos3_scalarCubeFamily_localize

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) {Q E : ℝ}
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ m : ℤ, |θ i-(m : ℝ)/q| ≤ E) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Q^Fintype.card I ∧
      ∃ a : I → ℤ, ∀ i, |θ i-(a i : ℝ)/D| ≤ E := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D,hDp,?_,(fun i => (rest i : ℤ)*m i),?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ _i : I, Q := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
      _ = Q^Fintype.card I := by simp
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ)*rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ)*m i : ℤ) : ℝ)/(D : ℝ) = (m i : ℝ)/q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

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

theorem length_small_grid_bound {N V L C ζ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hsize : N ≤ V * L ^ t) (hsmall : L ≤ C / ζ ^ c) :
    N ≤ V * C ^ t / ζ ^ (c * t) := by
  calc
    _ ≤ V * L ^ t := hsize
    _ ≤ V * (C / ζ ^ c) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hsmall t) hV
    _ = _ := by rw [div_pow, pow_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales
namespace OAI

section

namespace Erdos3

theorem localizationRadius_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε1 : ε ≤ 1) :
    localizationRadius U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  unfold localizationRadius
  apply (div_le_one (by positivity)).mpr
  linarith

theorem localizationRadius_scale {U ε : ℝ} (hU : 1 ≤ U) :
    U ^ 2 * localizationRadius U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius
  field_simp

theorem localizationMesh_scale {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    (2 * U ^ 3 / localizationRadius U ε) * localizationMesh U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationMesh
  field_simp
  ring

theorem localizationRadius_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationRadius U ε * localizationLengthBudget U ε W * ε = 32 * U ^ 4 * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationLengthBudget
  field_simp
  ring

theorem localization_inverse_length_error {U ε W L : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hW : 1 ≤ W) (hL : 0 < L)
    (hlen : localizationLengthBudget U ε W ≤ L) :
    2 * U ^ 3 / (localizationRadius U ε * L) ≤ ε / 4 := by
  have hr := localizationRadius_pos hU hε
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hr.le) hε.le
  rw [localizationRadius_length hU hε] at hmul
  have hp : U ^ 3 ≤ U ^ 4 := pow_le_pow_right₀ hU (by decide : 3 ≤ 4)
  have hprod : U ^ 4 ≤ U ^ 4 * W := le_mul_of_one_le_right (by positivity) hW
  have hp0 : 0 ≤ U ^ 3 := by positivity
  apply (div_le_iff₀ (mul_pos hr hL)).mpr
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricLocalizationThreshold
namespace OAI

section

namespace Erdos3

theorem localizationThreshold_step {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ)
    {i m : ℕ} (hi : i + 1 ≤ m) :
    localizationThreshold U ζ m + U ^ 2 * localizationThreshold U ζ (i + 1) ≤
      localizationThreshold U ζ i := by
  have hε := localizationThreshold_antitone hU hζ.le hi
  have hη := localizationThreshold_pos hU hζ (i + 1)
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : localizationThreshold U ζ i =
      2 * U ^ 2 * localizationThreshold U ζ (i + 1) := by
    have hC : 2 * U ^ 2 ≠ 0 := by positivity
    unfold localizationThreshold
    rw [pow_succ]
    field_simp
    exact pow_succ' _ _
  rw [he]
  nlinarith

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

theorem scaled_grid_approximation {M : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ) (d : ℕ)
    {E H : ℝ} (hclose : |(k.val : ℝ) / M - (a : ℝ) / d| ≤ E) (hE : M * E ≤ H) :
    |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) - M * ((a : ℝ) / d) =
      (M : ℝ) * ((k.val : ℝ) / M - (a : ℝ) / d) := by field_simp
  rw [he, abs_mul, abs_of_pos hM']
  exact (mul_le_mul_of_nonneg_left hclose hM'.le).trans hE

theorem grid_approximation_numerator_bound {M Q H d : ℕ} (hM : 0 < M)
    (hd : 0 < d) (hdQ : d ≤ Q) (k : Fin M) (a : ℤ)
    (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |a| ≤ (Q : ℤ) * (H + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdQ' : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
  have hk : (k.val : ℝ) < M := by exact_mod_cast k.isLt
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hmH : (H : ℝ) ≤ M * H := le_mul_of_one_le_left hH hM'
  obtain ⟨hl, hu⟩ := abs_le.mp hclose
  have hquot : |(a : ℝ) / d| ≤ H + 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_div, abs_of_pos hd'] at hquot
  have ha := (div_le_iff₀ hd').mp hquot
  have hbound : |(a : ℝ)| ≤ (Q : ℝ) * (H + 1) :=
    ha.trans (by nlinarith)
  exact_mod_cast hbound

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

theorem mem_rationalGridMajorSet {M Q H d : ℕ} (hM : 0 < M) (hd : 0 < d) (hdQ : d ≤ Q)
    (k : Fin M) (a : ℤ) (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    k ∈ rationalGridMajorSet M Q H := by
  classical
  have ha := grid_approximation_numerator_bound hM hd hdQ k a hclose
  unfold rationalGridMajorSet
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_range.mpr (by omega), Finset.mem_biUnion.mpr ?_⟩
  refine ⟨a, Finset.mem_Icc.mpr (abs_le.mp ha), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose⟩

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

theorem inverse_power_mono {A B ζ : ℝ} {a b : ℕ}
    (hB : 0 ≤ B) (hAB : A ≤ B) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hab : a ≤ b) :
    A / ζ ^ a ≤ B / ζ ^ b := by
  exact div_le_div₀ hB hAB (pow_pos hζ _)
    (pow_le_pow_of_le_one hζ.le hζ1 hab)

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem lengthAwareSpectrumCover_card {K : Type*} [Fintype K]
    (cover : ℝ → Finset K) {C L V A ζ : ℝ} {c t a : ℕ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ((cover ζ).card : ℝ) ≤ A / ζ ^ a) :
    ((lengthAwareSpectrumCover C L c cover ζ).card : ℝ) ≤
      A / ζ ^ a + V * C ^ t / ζ ^ (c * t) := by
  classical
  unfold lengthAwareSpectrumCover
  split_ifs with hstart
  · exact hcover.trans (le_add_of_nonneg_right (by positivity))
  · rw [Finset.card_univ]
    have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
    exact hb.trans (le_add_of_nonneg_left (by positivity))

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem localizationLengthBudget_threshold_eq (U ζ W : ℝ) (m : ℕ) :
    localizationLengthBudget U (localizationThreshold U ζ m) W =
      256 * U ^ 6 * W * (2 * U ^ 2) ^ (m * 2) / ζ ^ 2 := by
  simp only [localizationLengthBudget, localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcLengthBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcLengthBudget n U ζ =
      256 * U ^ 6 * (localizedMajorArcBudget n U ζ + 1) *
        (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2 :=
  localizationLengthBudget_threshold_eq U ζ (localizedMajorArcBudget n U ζ + 1) (n + 1)

theorem localizedMajorArcErrorBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcErrorBudget n U ζ =
      localizedMajorArcBudget n U ζ *
        (256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2) ^ (n + 1) := by
  unfold localizedMajorArcErrorBudget
  rw [localizationLengthBudget_threshold_eq]
  simp only [mul_one]

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

theorem localizedMajorArcBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ = majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n :=
  localizedMajorArcBudget_eq_power n hU hζ

theorem localizedMajorArcLengthBudget_le_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    localizedMajorArcLengthBudget n U ζ ≤
      majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n := by
  have hp : 0 < ζ ^ majorArcBiasExponent n := pow_pos hζ _
  have hp1 : ζ ^ majorArcBiasExponent n ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hone : (1 : ℝ) ≤ 1 / ζ ^ majorArcBiasExponent n := (le_div_iff₀ hp).mpr (by simpa)
  have hC := (majorArcLocalizationConstant_pos n hU).le
  rw [localizedMajorArcLengthBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  have he (x : ℝ) : 256 * U ^ 6 * x * (2 * U ^ 2) ^ ((n + 1) * 2) =
      majorArcLocalizationConstant n U * x := by
    unfold majorArcLocalizationConstant
    ring
  rw [he]
  calc
    _ ≤ majorArcLocalizationConstant n U *
        (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n +
          1 / ζ ^ majorArcBiasExponent n) / ζ ^ 2 := by gcongr
    _ = _ := by
      simp only [majorArcLengthConstant, majorArcLengthExponent, pow_add]
      ring

theorem localizedMajorArcErrorBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcErrorBudget n U ζ =
      majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n := by
  rw [localizedMajorArcErrorBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  change (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n) *
    (majorArcLocalizationConstant n U / ζ ^ 2) ^ (n + 1) = _
  simp only [majorArcErrorConstant, majorArcErrorExponent, div_pow, pow_add, pow_mul]
  ring

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

theorem majorArc_denominator_le_cover (n j : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have he := (majorArcErrorConstant_pos n hU).le
  have hC := (majorArcCoverConstant_one_le n j hU hV).trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hle : (majorArcBiasConstant n U * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    nlinarith only [mul_nonneg hV he]
  calc
    _ = (majorArcBiasConstant n U * U ^ (n + 1)) ^ j / ζ ^ (majorArcBiasExponent n * j) := by
      rw [localizedMajorArcBudget_constant n hU hζ, div_mul_eq_mul_div, div_pow, pow_mul]
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

theorem majorArc_scaled_error_le_cover (n j : ℕ) {U V ζ R P : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hscale : R / P ≤ V) :
    R * (localizedMajorArcErrorBudget n U ζ / P) ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have hE := (majorArcErrorConstant_pos n hU).le
  have hQ := (majorArcBiasConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  have hC : 0 ≤ majorArcCoverConstant n j U V :=
    le_trans (by norm_num) (majorArcCoverConstant_one_le n j hU hV)
  have hle : V * majorArcErrorConstant n U ≤ majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    linarith only [hd]
  rw [localizedMajorArcErrorBudget_constant n hU hζ]
  calc
    _ = (R / P) * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) := by ring
    _ ≤ V * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = (V * majorArcErrorConstant n U) / ζ ^ majorArcErrorExponent n := by ring
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

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

theorem uniformBlockSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L ζ).card : ℝ) ≤
      uniformBlockSpectrumCardBudget n (Fintype.card J) t U V W ζ := by
  apply lengthAwareSpectrumCover_card _ hL hW (majorArcSpectrumConstant_nonneg _ _ _ _)
    (majorArcLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact uniformMajorArcCover_card J M n hU hV hζ hζ1

theorem uniformBlockSpectrum_tail {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
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

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumSize
namespace OAI

section

namespace Erdos3

theorem uniformBlockRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    0 < uniformBlockRetainedBias n j t U V W ε ∧
      uniformBlockRetainedBias n j t U V W ε ≤ 1 ∧
      uniformBlockSpectrumAccuracyConstant n j t U V W *
        uniformBlockRetainedBias n j t U V W ε ≤ ε := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  have hpos : 0 < uniformBlockRetainedBias n j t U V W ε :=
    lt_min (by norm_num) (div_pos hε (by linarith))
  refine ⟨hpos, min_le_left _ _, ?_⟩
  calc
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        uniformBlockRetainedBias n j t U V W ε :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    _ = ε := by field_simp

end Erdos3

end

section

namespace Erdos3

theorem uniformBlockRetainedBias_eq (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε1 : ε ≤ 1) :
    uniformBlockRetainedBias n j t U V W ε =
      ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  apply min_eq_right
  apply (div_le_iff₀ (by linarith)).mpr
  linarith

theorem uniformBlockSpectrumCardBudget_le_accuracy_power (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    uniformBlockSpectrumCardBudget n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n j t hU hW hε
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hb : 0 ≤ W * majorArcLengthConstant n U ^ t := by positivity
  have ha := inverse_power_mono hA le_rfl hζ hζ1
    (le_max_left (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  have hp := inverse_power_mono hb le_rfl hζ hζ1
    (le_max_right (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  unfold uniformBlockSpectrumCardBudget
  apply (add_le_add ha hp).trans_eq
  rw [← add_div, uniformBlockRetainedBias_eq n j t hU hW hε1]
  simp only [uniformSpectrumSizeConstant, div_pow, div_div_eq_mul_div]

theorem uniformBlockSpectrumCover_polynomial_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
      uniformSpectrumSizeConstant n (Fintype.card J) t U V W /
        ε ^ max (majorArcSpectrumExponent n (Fintype.card J)) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  exact (uniformBlockSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize).trans
    (uniformBlockSpectrumCardBudget_le_accuracy_power n (Fintype.card J) t hU hW hε hε1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_padded_boolean_labels {α : Type*} [DecidableEq α]
    (s : Finset α) (h : ℕ) (hs : s.card ≤ h) :
    ∃ label : Fin h → Option α, ∀ a, (∃ i, label i = some a) ↔ a ∈ s := by
  classical
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let label : Fin h → Option α := fun i =>
    if hi : i.val < s.card then some (e.symm ⟨i.val, hi⟩).val else none
  refine ⟨label, ?_⟩
  intro a
  constructor
  · rintro ⟨i, hi⟩
    dsimp [label] at hi
    split_ifs at hi with hc
    · have ha := Option.some.inj hi
      exact ha ▸ (e.symm ⟨i.val, hc⟩).property
  · intro ha
    let j := e ⟨a, ha⟩
    let i : Fin h := ⟨j.val, lt_of_lt_of_le j.isLt hs⟩
    refine ⟨i, ?_⟩
    dsimp [label, i]
    rw [if_pos j.isLt]
    change some (e.symm (e ⟨a, ha⟩)).val = some a
    simp

theorem booleanFeature_product {α ι R : Type*} [DecidableEq α] [Fintype ι] [CommMonoidWithZero R]
    (label : ι → Option α) (s : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ s) (t : Finset α) :
    (∏ i, (booleanFeature (label i) t : R)) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    apply Finset.prod_eq_one
    intro i _
    cases hi : label i with
    | none => rfl
    | some a =>
      have ha := hst ((hlabel a).mp ⟨i, hi⟩)
      simp only [booleanFeature, ha, ite_true]
  · rw [if_neg hst]
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hst
    obtain ⟨i, hi⟩ := (hlabel a).mpr has
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, booleanFeature, hat, ite_false]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionCoordinateResampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G R : Type*} [DecidableEq R] {X : G → R → Type*}

theorem expect_resampleGroupCoordinates [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) :
    (𝔼 c : ∀ g r, X g r, 𝔼 t : ∀ g, X g (label g),
      F (resampleGroupCoordinates label c t)) = 𝔼 c : ∀ g r, X g r, F c := by
  have he := Fintype.expect_equiv (groupCoordinateResamplingEquiv (X := X) label)
    (fun p => F (resampleGroupCoordinates label p.1 p.2)) (fun p => F p.1)
    (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

theorem exists_frozen_group_bias [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) {ζ : ℝ}
    (hζ : ζ ≤ ‖𝔼 c : ∀ g r, X g r, F c‖) :
    ∃ c : ∀ g r, X g r,
      ζ ≤ ‖𝔼 t : ∀ g, X g (label g), F (resampleGroupCoordinates label c t)‖ := by
  rw [← expect_resampleGroupCoordinates label F] at hζ
  have h := hζ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty h
  exact ⟨c, hc⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem progressionCoordinates_resample {G R : Type*} [DecidableEq R]
    (N : G → R → ℕ) (u v : G → R → ℝ) (label : G → R)
    (c : ∀ g r, Fin (N g r)) (t : ∀ g, Fin (N g (label g))) :
    resampleGroupCoordinates label (fun g r => u g r+v g r*((c g r).val : ℝ))
      (fun g => u g (label g)+v g (label g)*((t g).val : ℝ)) =
        (fun g r => u g r+v g r*((resampleGroupCoordinates label c t g r).val : ℝ)) := by
  funext g r
  by_cases hr : r = label g
  · subst r
    simp [resampleGroupCoordinates]
  · simp [resampleGroupCoordinates, hr]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem booleanAffine_resample {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) (g : G) :
    (∑ r, (booleanFeature r t : ℝ)*resampleGroupCoordinates label c x g r) =
      (booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (label g))]
  rw [resampleGroupCoordinates_selected]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [resampleGroupCoordinates, Function.update_of_ne (Finset.ne_of_mem_erase hr)]

theorem booleanBlockValue_resample {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) :
    booleanBlockValue (resampleGroupCoordinates label c x) t =
      ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g) := by
  simp only [booleanBlockValue, booleanAffine_resample]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_degreeOf_le {α ι : Type*} [DecidableEq α]
    (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) (j : ι) (d : ℕ)
    (hf : ∀ t ∈ s.powerset, (f t).degreeOf j ≤ d) :
    (booleanCoefficient f s).degreeOf j ≤ d := by
  classical
  unfold booleanCoefficient
  apply (MvPolynomial.degreeOf_sum_le j s.powerset _).trans
  apply Finset.sup_le
  intro t ht
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc]
  exact (MvPolynomial.degreeOf_C_mul_le _ j _).trans (hf t ht)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem frozenBooleanFactor_degree {G α : Type*} [DecidableEq G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g j : G) :
    (frozenBooleanFactor label c t g).degreeOf j ≤ if g=j then 1 else 0 := by
  unfold frozenBooleanFactor
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, eq_comm]
    exact le_rfl
  · simp only [MvPolynomial.degreeOf_C]
    split_ifs <;> omega

theorem frozenBooleanProduct_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (t : Finset α) (j : G) : (∏ g, frozenBooleanFactor label c t g).degreeOf j ≤ 1 := by
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  apply (Finset.sum_le_sum (fun g _ => frozenBooleanFactor_degree label c t g j)).trans
  simp

theorem frozenBooleanPhasePolynomial_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (j : G) : (frozenBooleanPhasePolynomial label c ξ).degreeOf j ≤ 1 := by
  unfold frozenBooleanPhasePolynomial
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro s _
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  exact booleanCoefficient_degreeOf_le _ s j 1
    (fun t _ => frozenBooleanProduct_degree label c t j)

theorem frozenBooleanPhasePolynomial_eval {G α : Type*} [Fintype G] [Fintype α]
    [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (x : G → ℝ) :
    MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ) =
      booleanBlockPhase ξ (resampleGroupCoordinates label c x) := by
  simp only [frozenBooleanPhasePolynomial, booleanBlockPhase, map_sum, map_mul,
    MvPolynomial.eval_C, booleanCoefficient_map, map_prod, frozenBooleanFactor,
    map_add, MvPolynomial.eval_X]
  have he : booleanBlockValue (resampleGroupCoordinates label c x) =
      (fun t => ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g)) := by
    funext t
    exact booleanBlockValue_resample label c x t
  rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrideProductBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem additiveBoxDifference_const_mul {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : R) (F : (∀ i, X i) → Z → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => a*F x t) u v z =
      a*additiveBoxDifference n F u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← mul_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_booleanCoefficient {R Z α : Type*} [CommRing R]
    [DecidableEq α] (n : ℕ) {X : Fin n → Type*}
    (F : Finset α → (∀ i, X i) → Z → R) (s : Finset α)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => booleanCoefficient (fun r => F r x t) s) u v z =
      booleanCoefficient (fun r => additiveBoxDifference n (F r) u v z) s := by
  unfold booleanCoefficient
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul]

theorem full_coefficient_eq_mixed_difference {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) :
    P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      additiveBoxDifference n (fun x (_ : Unit) => MvPolynomial.eval x P)
        (fun _ => 1) (fun _ => 0) () := by
  have he : (fun x (_ : Unit) => MvPolynomial.eval x P) =
      (fun x (_ : Unit) => multiaffineExpansion
        (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x) := by
    funext x t
    exact multiaffinePolynomial_eval P hP x
  rw [he]
  have h := multiaffineExpansion_box_difference n (X := fun _ => ℝ)
    (fun S (_ : Unit) => P.coeff (SquarefreeIndex.ofFinset S).val)
    (fun _ (x : ℝ) => x) (fun _ => 1) (fun _ => 0) ()
  simpa using h.symm

theorem affine_product_full_difference (n : ℕ) (a b : Fin n → ℝ) :
    additiveBoxDifference n (fun x (_ : Unit) => ∏ i, (a i*x i+b i))
      (fun _ => 1) (fun _ => 0) () = ∏ i, a i := by
  have h := additiveBoxDifference_product n (X := fun _ => ℝ) (fun _ : Unit => (1 : ℝ))
    (fun i (x : ℝ) => a i*x+b i) (fun _ => 1) (fun _ => 0) ()
  simpa using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem frozenBooleanBlock_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ) (t : Finset α) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockValue (resampleGroupCoordinates label c x) t)
      (fun _ => 1) (fun _ => 0) () = ∏ i, (booleanFeature (label i) t : ℝ) := by
  simp_rw [booleanBlockValue_resample]
  exact affine_product_full_difference n _ _

theorem frozenBooleanJet_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (S s : Finset α) (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanCoefficient
        (fun t => booleanBlockValue (resampleGroupCoordinates label c x) t) s)
      (fun _ => 1) (fun _ => 0) () = if s=S then 1 else 0 := by
  rw [additiveBoxDifference_booleanCoefficient]
  simp_rw [frozenBooleanBlock_full_difference, booleanFeature_product label S hlabel]
  exact booleanCoefficient_monomial S s

theorem frozenBooleanPhase_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x))
      (fun _ => 1) (fun _ => 0) () = ξ S := by
  unfold booleanBlockPhase
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul,
    frozenBooleanJet_full_difference n label c S _ hlabel]
  simp

theorem frozenBooleanPhasePolynomial_coefficient {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    (frozenBooleanPhasePolynomial label c ξ).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = ξ S := by
  rw [full_coefficient_eq_mixed_difference _ (frozenBooleanPhasePolynomial_degree label c ξ)]
  have he : (fun x (_ : Unit) => MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ)) =
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x)) := by
    funext x t
    exact frozenBooleanPhasePolynomial_eval label c ξ x
  rw [he]
  exact frozenBooleanPhase_full_difference n label c ξ S hlabel

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_strided_selected_entry {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (N s : Fin (n+1) → Option α → ℕ) (u : Fin (n+1) → Option α → ℝ)
    (ξ : Finset α → ℝ) (label : Fin (n+1) → Option α) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S)
    (hNpos : ∀ g r, 0 < N g r) (hs : ∀ g, 0 < s g (label g))
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g (label g))
    (hbias : ζ ≤ ‖𝔼 x : ∀ g r, Fin (N g r),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ g, (s g (label g) : ℝ) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        ∏ g, ((s g (label g) : ℝ)*(N g (label g) : ℝ)) := by
  let : ∀ g r, Nonempty (Fin (N g r)) := fun g r => ⟨⟨0,hNpos g r⟩⟩
  let F := fun x : ∀ g r, Fin (N g r) =>
    character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
      CircleFourier.Circle)
  obtain ⟨c,hc⟩ := exists_frozen_group_bias label F hbias
  let b := fun g r => u g r+(s g r : ℝ)*((c g r).val : ℝ)
  let P := frozenBooleanPhasePolynomial label b ξ
  have hphase (t : ∀ g, Fin (N g (label g))) :
      F (resampleGroupCoordinates label c t) =
        character ((MvPolynomial.eval
          (fun g => u g (label g)+(s g (label g) : ℝ)*((t g).val : ℝ)) P : ℝ) :
          CircleFourier.Circle) := by
    dsimp only [F,P]
    rw [frozenBooleanPhasePolynomial_eval]
    dsimp only [b]
    rw [progressionCoordinates_resample]
  simp_rw [hphase] at hc
  have h := fin_multiaffine_strided_bias P (frozenBooleanPhasePolynomial_degree label b ξ)
    (fun g => N g (label g)) (fun g => s g (label g)) hs (fun g => u g (label g)) hζ hN hc
  simpa only [P, frozenBooleanPhasePolynomial_coefficient (n+1) label b ξ S hlabel] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stride_product_le {I : Type*} [Fintype I] (s : I → ℕ) {R : ℝ}
    (hs : ∀ i, (s i : ℝ) ≤ R) : (∏ i, (s i : ℝ)) ≤ R^Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, R := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hs i)
    _ = _ := by simp

theorem stride_product_error_le {I : Type*} [Fintype I] (N s : I → ℕ)
    (hN : ∀ i, 0 < N i) (hs : ∀ i, 0 < s i) {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    A/(C*∏ i, ((s i : ℝ)*(N i : ℝ))) ≤ A/(C*∏ i, (N i : ℝ)) := by
  have hp : (0 : ℝ) < ∏ i, (N i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hN i)
  apply div_le_div_of_nonneg_left hA (mul_pos hC hp)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
  intro i _
  have hsi : (1 : ℝ) ≤ s i := by exact_mod_cast hs i
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hsi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGridBoundaryConstant_pos (I : Type*) [Fintype I] :
    0 < scalarCubeGridBoundaryConstant I := by
  unfold scalarCubeGridBoundaryConstant
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
  positivity

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoarseLocalizationError
namespace OAI

section

namespace Erdos3

theorem coarse_localization_error {U B C D H T M r δ L η : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (_hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hL : 0 < L) (hη : 0 ≤ η)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * r + (D + H / r) * (M / L)) + C * ((T + B * H / r) * δ + B * η) ≤
      U ^ 2 * r + 2 * U ^ 3 / (r * L) + (2 * U ^ 3 / r) * δ + U ^ 2 * η := by
  have hU0 : 0 < U := by linarith
  have hsum : D + H / r ≤ 2 * U / r := by
    apply (le_div_iff₀ hr).mpr
    have hDr : D * r ≤ U := (mul_le_mul_of_nonneg_right hD hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have he : (D + H / r) * r = D * r + H := by field_simp
    rw [he]
    linarith
  have hsum' : T + B * H / r ≤ 2 * U ^ 2 / r := by
    apply (le_div_iff₀ hr).mpr
    have hTr : T * r ≤ U := (mul_le_mul_of_nonneg_right hT hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have hBH : B * H ≤ U ^ 2 := by nlinarith [mul_le_mul hB hH hH0 hU0.le]
    have he : (T + B * H / r) * r = T * r + B * H := by field_simp
    rw [he]
    nlinarith
  calc
    _ ≤ U * (U * r + (2 * U / r) * (U / L)) + U * ((2 * U ^ 2 / r) * δ + U * η) := by
      gcongr
    _ = _ := by field_simp; ring

theorem polynomial_localization_error {U B C D H T M L η ε W : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hL : 0 < L) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ L) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * localizationRadius U ε + (D + H / localizationRadius U ε) * (M / L)) +
      C * ((T + B * H / localizationRadius U ε) * localizationMesh U ε + B * η) ≤ ε + U ^ 2 * η := by
  have hc := coarse_localization_error hU hB0 hC0 hD0 hH0 hT0 hM0 hB hC hD hH hT hM
    (localizationRadius_pos hU hε) (localizationRadius_le_one hU hε1)
    (localizationMesh_pos hU hε).le hL hη hA0 hA
  rw [localizationRadius_scale hU, localizationMesh_scale hU hε] at hc
  have hi := localization_inverse_length_error hU hε hW hL hlen
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

theorem residueCellIntegerPoint_normalized {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) :
    (fun i => (residueCellIntegerPoint L N K m res k t i : ℝ) / L) =
      residueCellPosition L N K m res k t := by
  funext i
  simp only [residueCellIntegerPoint, scalarResidueGridPoint, residueCellPosition,
    progressionCellCorner, paddedResidueOffset, paddedResidueStep,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem cellLength_pos : 0 < d.cellLength :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).1

theorem cellLength_lower : d.mesh * d.length / (2 * d.modulusBound) ≤ (d.cellLength : ℝ) :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).2.2.1

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem point_scale (z : IntegerScalarCubeBox I d.length) (i : Option I) :
    (d.length : ℝ) * d.point z i = (z i : ℝ) := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  change (d.length : ℝ) * ((z i : ℝ) / d.length) = _
  exact mul_div_cancel₀ _ hL

theorem cell_scale (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => d.integerOffset k i + (d.modulus i : ℝ) * (t i).val := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  have he := residueCellIntegerPoint_normalized d.length d.cellLength d.cellCount d.modulus d.residue k t
  funext i
  have hi := congrFun he i
  change (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) /
    d.length = d.cell k t i at hi
  calc
    _ = (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) := by
      rw [← hi]
      exact mul_div_cancel₀ _ hL
    _ = _ := by
      simp only [residueCellIntegerPoint, scalarResidueGridPoint, integerOffset,
        Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem lengthLoss_pos : 0 < d.lengthLoss := by
  have hM : 0 < d.modulusBound := (d.modulus_pos none).trans_le (d.modulus_le none)
  exact div_pos (by positivity) d.mesh_pos

theorem length_le_lengthLoss_mul_cellLength :
    (d.length : ℝ) ≤ d.lengthLoss * d.cellLength := by
  have hM : (0 : ℝ) < d.modulusBound := by
    exact_mod_cast (d.modulus_pos none).trans_le (d.modulus_le none)
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d.modulusBound)).mp d.cellLength_lower
  unfold lengthLoss
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ d.mesh_pos).mpr
  nlinarith

end ScalarCubeLocalizationData

theorem reciprocal_product_le_of_lengths {J : Type*} [Fintype J]
    (a b c : J → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hlen : ∀ j, a j ≤ c j * b j) {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, b j) ≤ Q * (∏ j, c j) / (∏ j, a j) := by
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun j _ => (ha j).le) (fun j _ => hlen j)
  rw [Finset.prod_mul_distrib] at hprod
  apply (div_le_div_iff₀ (Finset.prod_pos (fun j _ => hb j)) (Finset.prod_pos (fun j _ => ha j))).mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hQ

theorem scalarCubeCell_inverse_product {J : Type*} [Fintype J]
    (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (d : ∀ j, ScalarCubeLocalizationData (I j)) {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, ((d j).cellLength : ℝ)) ≤
      Q * (∏ j, (d j).lengthLoss) / (∏ j, ((d j).length : ℝ)) := by
  apply reciprocal_product_le_of_lengths _ _ _ _ _ (fun j => (d j).length_le_lengthLoss_mul_cellLength) hQ
  · intro j
    exact_mod_cast (d j).length_pos
  · intro j
    exact_mod_cast (d j).cellLength_pos

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

namespace FiniteCoefficientSlice

end FiniteCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformStridedBlockEntry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_bounded_stride_entry {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (s : Fin (n+1) → Option α → ℕ)
    (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ) (S : Finset α)
    (hS : S.card ≤ n+1) (hs : ∀ g r, 0 < s g r) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * R^(n+1) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  obtain ⟨label,hlabel⟩ := exists_padded_boolean_labels S (n+1) hS
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ g, 0 < N g := fun g => by exact_mod_cast hQ.trans_le (hN g)
  obtain ⟨D,hD,hDQ,m,hm⟩ := booleanBlockPhase_strided_selected_entry (fun g _ => N g) s u ξ
    label S hlabel (fun g _ => hNp g) (fun g => hs g (label g)) hζ hN hbias
  refine ⟨D,hD,hDQ.trans ?_,m,hm.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hQ.le
    simpa only [Fintype.card_fin] using stride_product_le (fun g => s g (label g))
      (fun g => hR g (label g))
  · simpa only [one_mul] using stride_product_error_le N (fun g => s g (label g)) hNp
      (fun g => hs g (label g)) (by norm_num : (0 : ℝ) < 1) hQ.le

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeCoordinates
namespace OAI

section

namespace Erdos3

theorem ScalarCubeLocalizationData.affine_point_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (z : IntegerScalarCubeBox I d.length) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.point z i) =
      affineCubeCoordinates u v (fun i => (z i : ℝ)) := by
  congr 1
  funext i
  exact d.point_scale z i

theorem ScalarCubeLocalizationData.affine_cell_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => (u i + (v i : ℝ) * d.integerOffset k i) +
        ((v i * d.modulus i : ℕ) : ℝ) * (t i).val := by
  rw [d.cell_scale]
  funext i
  simp only [affineCubeCoordinates, Nat.cast_mul]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCutoffLengthBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeCutoffLipschitzConstant_eq (I : Type*) [Fintype I] (A r : ℝ≥0) :
    (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / r := by
  simp only [scalarCubeCutoffLipschitzConstant, scalarCubeCutoffDerivativeNumerator,
    NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialScalarCubeLength
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ s.length)

theorem polynomialLocalizationData_cellLength :
    W ≤ ((s.polynomialLocalizationData A hA h hε hε1 hW hlen).cellLength : ℝ) := by
  let d := s.polynomialLocalizationData A hA h hε hε1 hW hlen
  have hM : (0 : ℝ) < s.modulusBound := by
    exact_mod_cast (s.modulus_pos none).trans_le (s.modulus_le none)
  have hδ := localizationMesh_pos h.one_le hε
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  apply le_trans _ d.cellLength_lower
  change W ≤ localizationMesh U ε * s.length / (2 * s.modulusBound)
  apply (le_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right h.modulus_le (by linarith : 0 ≤ W)
  nlinarith

theorem polynomialLocalizationData_error {η : ℝ} (hη : 0 ≤ η) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).error η ≤ ε + U ^ 2 * η := by
  have hM : 0 < s.modulusBound := (s.modulus_pos none).trans_le (s.modulus_le none)
  have hC0 : 0 ≤ paddedResidueDensityCap I s.modulusBound := by
    have hc := scalarCubeResidueDensityCap_pos I s.modulusBound hM
    unfold paddedResidueDensityCap
    positivity
  have hG0 : 0 ≤ 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) := by
    have hg := scalarCubeGridBoundaryConstant_pos I
    have hv := scalarCubeDomain_volumeReal_pos I
    positivity
  have hH0 : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator
    positivity
  have he := polynomial_localization_error h.one_le s.weightBound.coe_nonneg hC0 hG0 hH0
    s.weightLipschitz.coe_nonneg (Nat.cast_nonneg s.modulusBound)
    h.weight_le h.density_le h.grid_le h.derivative_le h.weightLipschitz_le h.modulus_le
    (by exact_mod_cast s.length_pos) hη hε hε1 hW hlen
    (scalarCubeBoundaryConstant_pos I).le h.boundary_le
  let r : ℝ≥0 := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
  have hr : (r : ℝ) = localizationRadius U ε := rfl
  have hq : (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / localizationRadius U ε :=
    scalarCubeCutoffLipschitzConstant_eq I A r
  change (s.weightBound : ℝ) * scalarCubeResidueCutoffBudget I A r s.length s.modulusBound +
    paddedResidueDensityCap I s.modulusBound *
      (((s.weightLipschitz : ℝ) + s.weightBound * scalarCubeCutoffLipschitzConstant I A r) *
        localizationMesh U ε + s.weightBound * η) ≤ _
  unfold scalarCubeResidueCutoffBudget
  rw [hq, hr]
  simpa only [mul_div_assoc] using he

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NormalizedScalarCubeSource

theorem polynomialLocalizationData_lengthLoss {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {U ε W : ℝ} (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : 1 ≤ W) (hlen : localizationLengthBudget U ε W ≤ s.length) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).lengthLoss ≤
      localizationLengthBudget U ε 1 := by
  change 2 * (s.modulusBound : ℝ) / localizationMesh U ε ≤ _
  calc
    _ ≤ 2 * U / localizationMesh U ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.modulus_le (by norm_num))
        (localizationMesh_pos h.one_le hε).le
    _ = _ := by
      have hU : U ≠ 0 := ne_of_gt (by linarith [h.one_le])
      unfold localizationMesh localizationLengthBudget
      field_simp
      ring

end NormalizedScalarCubeSource

theorem polynomialScalarCube_inverse_product {J : Type*} [Fintype J]
    (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (s : ∀ j, NormalizedScalarCubeSource (I j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : 1 ≤ W) (hlen : ∀ j, localizationLengthBudget U ε W ≤ (s j).length)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, (((s j).polynomialLocalizationData A hA (h j) hε hε1 hW (hlen j)).cellLength : ℝ)) ≤
      Q * (localizationLengthBudget U ε 1) ^ Fintype.card J / ∏ j, ((s j).length : ℝ) := by
  let d j := (s j).polynomialLocalizationData A hA (h j) hε hε1 hW (hlen j)
  have hp : (∏ j, (d j).lengthLoss) ≤ (localizationLengthBudget U ε 1) ^ Fintype.card J := by
    calc
      _ ≤ ∏ _j : J, localizationLengthBudget U ε 1 :=
        Finset.prod_le_prod (fun j _ => (d j).lengthLoss_pos.le)
          (fun j _ => (s j).polynomialLocalizationData_lengthLoss A hA (h j) hε hε1 hW (hlen j))
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  exact (scalarCubeCell_inverse_product I d hQ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hQ) (by positivity))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_bounded_stride_major_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (s : Fin (n+1) → Option α → ℕ)
    (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n+1)
    (hs : ∀ g r, 0 < s g r) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (multiaffineBiasBudget n ζ*R^(n+1))^J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S-(a S : ℝ)/D| ≤
        multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  have h := exists_common_rational_approximations (fun S : J => ξ S)
    (fun S => booleanBlockPhase_bounded_stride_entry N s u ξ S (hJ S S.property) hs hR hζ hN hbias)
  simpa only [Fintype.card_coe] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affine_weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : Fin (n + 1) → ScalarCubeLocalizationData I) (τ : Fin (n + 2) → ℝ)
    (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (ξ : Finset I → ℝ)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    {R : ℝ} (hR : ∀ j i, ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) * R ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) / ∏ j, ((d j).cellLength : ℝ) := by
  let F : (Fin (n + 1) → Option I → ℝ) → ℂ := fun x => character ((booleanBlockPhase ξ
    (fun j => affineCubeCoordinates (u j) (v j) (fun i => ((d j).length : ℝ) * x j i)) : ℝ) : CircleFourier.Circle)
  have hF (x) : ‖F x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsource (z : ∀ j, IntegerScalarCubeBox I (d j).length) :
      F (fun j => (d j).point (z j)) = character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    simp only [ScalarCubeLocalizationData.affine_point_scale]
  have hs : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖ := by simpa only [hsource] using hbias
  obtain ⟨k, _, hphase⟩ := scalarCubeFamily_localize (fun _ => I) d τ hτ herror F hF hs
  have hcell (t : ∀ j, Option I → Fin (d j).cellLength) :
      F (fun j => (d j).cell (k j) (t j)) = character ((booleanBlockPhase ξ (fun j i =>
        (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
          ((v j i * (d j).modulus i : ℕ) : ℝ) * (t j i).val) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    simp only [ScalarCubeLocalizationData.affine_cell_scale]
  have hm := Finset.expect_congr (s := Finset.univ) rfl (fun t _ => hcell t)
  have hp := hphase.trans_eq (congrArg norm hm)
  exact booleanBlockPhase_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j i => v j i * (d j).modulus i)
    (fun j i => u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) ξ J hJ
    (fun j i => Nat.mul_pos (hv j i) ((d j).modulus_pos i)) hR (hτ (Fin.last n)) hN hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {n : ℕ} {U ζ : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : localizedMajorArcLengthBudget n U ζ ≤ s.length)

theorem majorArcLocalizationData_cellLength :
    localizedMajorArcBudget n U ζ ≤
      ((s.majorArcLocalizationData A hA h hζ hζ1 hlen).cellLength : ℝ) := by
  exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (s.polynomialLocalizationData_cellLength A hA h
      (localizationThreshold_pos h.one_le hζ (n + 1))
      (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
      (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen)

theorem majorArcLocalizationData_error {i : ℕ} (hi : i + 1 ≤ n + 1) :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).error (localizationThreshold U ζ (i + 1)) ≤
      localizationThreshold U ζ i := by
  exact (s.polynomialLocalizationData_error A hA h
    (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen
    (localizationThreshold_pos h.one_le hζ (i + 1)).le).trans
      (localizationThreshold_step h.one_le hζ hi)

end NormalizedScalarCubeSource
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_affine_weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hU := (h 0).one_le
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hU hζ _
  have herr (j : Fin (n + 1)) : (d j).error (τ j.succ) ≤ τ j.castSucc :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hN (j : Fin (n + 1)) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hb : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := affine_weightedCubeBlock_major_arc d τ hτ herr u v hv ξ J hJ hstride hN hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have he := polynomialScalarCube_inverse_product (fun _ : Fin (n + 1) => I) s A hA h
    (localizationThreshold_pos hU hζ (n + 1))
    (localizationThreshold_le_one hU hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n hU hζ]) hlen
    (localizedMajorArcBudget_pos n hU hζ).le
  simpa only [Fintype.card_fin, localizedMajorArcErrorBudget, localizedMajorArcBudget,
    τ, Fin.val_last, d, NormalizedScalarCubeSource.majorArcLocalizationData] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_rationalGridMajorBox {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M)
    {D : ℕ} (hD : 0 < D) (hDQ : D ≤ Q) (a : J → ℤ) {E : ℝ}
    (hclose : ∀ j, |((k j).val : ℝ) / M - (a j : ℝ) / D| ≤ E)
    (hE : M * E ≤ H) : k ∈ rationalGridMajorBox J M Q H := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_rationalGridMajorSet hM hD hDQ (k j) (a j)
    (scaled_grid_approximation hM (k j) (a j) (D) (hclose j) hE)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dif_pos S.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem sum_eq_retained_add_spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ∑ k, f k = (∑ k ∈ S, f k) + spectrumTail S f := by
  calc
    _ = ∑ k, ((if k ∈ S then f k else 0) + (if k ∈ S then 0 else f k)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, add_zero, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, spectrumTail]

theorem product_spectrum_absolute_cap {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : Finset K) (hunit : ∀ b k, ‖c b k‖ ≤ 1) :
    (∑ k, ‖∏ b, c b k‖) ≤ S.card + spectrumTail S (fun k => ‖∏ b, c b k‖) := by
  rw [sum_eq_retained_add_spectrumTail S]
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ _k ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [one_pow] using norm_product_coefficients_le (fun b => c b k) (fun b => hunit b k)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniformBlockSpectrum_absolute_cap {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hunit : ∀ b k, ‖coeff b k‖ ≤ 1)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ) :
    (∑ k, ‖∏ b, coeff b k‖) ≤ uniformSpectrumAbsoluteCap n (Fintype.card J) t U V W := by
  classical
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW (by norm_num : (0 : ℝ) < 1)
  let S := uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n (Fintype.card J) t U V W 1)
  have ht := uniformBlockSpectrum_tail M n t coeff hU hV hW hL hζ hζ1 (by norm_num) hB hsize hminor hacc
  have hc : (S.card : ℝ) ≤ uniformSpectrumSizeConstant n (Fintype.card J) t U V W := by
    simpa only [one_pow, div_one] using uniformBlockSpectrumCover_polynomial_card J M n t
      hU hV hW hL (by norm_num : (0 : ℝ) < 1) le_rfl hsize
  exact (product_spectrum_absolute_cap coeff S hunit).trans (add_le_add hc ht)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affineWeightedCubeGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖affineWeightedCubeGridCoefficient s u v M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by simp only [norm_character, p.mean_const])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affineWeightedCubeGridCoefficient_mem_cover {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    {M : ℕ} (hM : 0 < M) (hscale : (M : ℝ) / ∏ j, ((s j).length : ℝ) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖affineWeightedCubeGridCoefficient s u v M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V) (majorArcCoverExponent n J.card) ζ := by
  have hU := (h 0).one_le
  obtain ⟨D, hD, hDb, a, ha⟩ := polynomial_affine_weightedCubeBlock_major_arc s A hA h hζ hζ1
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j))
    u v hv hstride (gridJetFrequency M J k) J hJ hk
  have hQ := (majorArc_denominator_le_cover n J.card hU hV hζ hζ1).trans (Nat.le_ceil _)
  have hH := (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDb.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineUniformSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_uniform_spectrum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    spectrumTail S (fun k => ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤ ε ∧
      (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card t U V W := by
  let c b := affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J
  have hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖c b k‖ ≤ δ := by
    intro δ hδ hδ1 hlength b k hk
    apply le_of_lt (lt_of_not_ge (fun hh => hk ?_))
    simpa only [Fintype.card_coe] using affineWeightedCubeGridCoefficient_mem_cover (s b) A hA (h b)
      hV hδ hδ1 (fun j => hlength.trans (hlen b j)) (u b) (v b) (hv b) (hstride b)
      hM (hscale b) J hJ k hh
  have hB' : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B := by simpa only [Fintype.card_coe] using hB
  have hsize' : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t := by simpa only [Fintype.card_coe] using hsize
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  constructor
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_tail M n t c hU hV hW hL
      hζ hζ1 hε.le hB' hsize' hminor hacc
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_absolute_cap M n t c hU hV hW hL
      hB' hsize' (fun b k => affineWeightedCubeGridCoefficient_norm_le_one (s b) (u b) (v b) M J k) hminor

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.affine_weightedCube_uniform_spectrum.{u_1, u_2} := @OAI.Erdos3.affine_weightedCube_uniform_spectrum.{u_1, u_2}
