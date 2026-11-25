-- Prove2me | solution 1 for GlobalTheory.Dyadic.dyadic_summation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:25.608346+00:00
-- url     : https://prove2.me/submissions/f2671c0b-bb14-4465-be84-af9a2f84391c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation
import Theorems.Thm_GlobalTheory_Dyadic_lintegral_mul_le_of_sq
import Theorems.Thm_GlobalTheory_Dyadic_exists_shell
import Theorems.Thm_GlobalTheory_Dyadic_exists_shell_down
import Theorems.Thm_GlobalTheory_Dyadic_piece_bound
import Theorems.Thm_GlobalTheory_Dyadic_tsum_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r kk : ℕ) (H₁ De D K K' : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧ D ≤ max (S x) (S' x) ^ (2 * r) ∧ Y x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ∧ Y' x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ i * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < S x) ∧ S' x ≤ 2 ^ i' * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < S' x) ∧ S x ≤ 2 ^ i * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (Real.sqrt (K * K') * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk) := by
  intro X _ ν A B S S' Y Y' r kk H De D K K' hA hB hS hS' hY hY' hr hkk hH hDe hD hK hK' hae h1 h2
  have hH0 : 0 < H := by linarith
  have hDe0 : 0 < De := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  let T : ℕ → ℕ → ℝ := fun i i' => (r * ((2 : ℝ) ^ i * 2 ^ i' * H) ^ (2 * r - 1) * De) ^ r
  have hT : ∀ i i', 0 < T i i' := fun i i' => by positivity
  let Q : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x | (0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧
      D ≤ ((2 : ℝ) ^ p.1 * 2 ^ p.2.1 * H) ^ (2 * r)) ∧
      S x ≤ 2 ^ p.1 * H ∧ (p.1 = 0 ∨ 2 ^ p.1 * H / 2 < S x) ∧
      S' x ≤ 2 ^ p.2.1 * H ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H / 2 < S' x) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, Q p := by
    filter_upwards [hae] with x ⟨_, _, s1, s2, y1, y2, hyy, hd, t1, t2⟩
    obtain ⟨i, hi, hi2⟩ := exists_shell (S x) H hH0
    obtain ⟨i', hi', hi2'⟩ := exists_shell (S' x) H hH0
    have a1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    have a2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
    have hm : max (S x) (S' x) ≤ (2 : ℝ) ^ i * 2 ^ i' * H := by
      refine max_le (hi.trans ?_) (hi'.trans ?_)
      · gcongr; exact le_mul_of_one_le_right (by positivity) a2
      · gcongr; exact le_mul_of_one_le_left (by positivity) a1
    have hm0 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith)
    have hmT : (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ≤ T i i' := by
      simp only [T]; gcongr
    obtain ⟨a, ha⟩ := exists_shell_down (Y x) (T i i') y1 (t1.trans hmT)
    obtain ⟨b, hb⟩ := exists_shell_down (Y' x) (T i i') y2 (t2.trans hmT)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b),
      ⟨y1, y2, hyy, hd.trans (pow_le_pow_left₀ hm0 hm _)⟩, hi, hi2, hi', hi2', ha, hb⟩
  set C : ℝ := Real.sqrt (K * K') * ((r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) *
    (2 ^ r / D) ^ kk) with hC
  have hC0 : 0 ≤ C := by positivity
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (Q (i, i', a, b)).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]; simp
    obtain ⟨⟨y1, y2, hyy, hd⟩, -, -, -, -, ⟨ha, -⟩, ⟨hb, -⟩⟩ := hx0
    dsimp only at hd ha hb ⊢
    have hTi := hT i i'
    have hyy' : T i i' / 2 ^ (a + 1) * (T i i' / 2 ^ (b + 1)) * D ≤ 2 ^ r := by
      refine le_trans ?_ hyy
      gcongr
    have key := piece_bound r kk H De D (2 ^ i) (2 ^ i') (2 ^ (a + 1)) (2 ^ (b + 1)) hr hkk hH hDe hD
      (one_le_pow₀ one_le_two) (one_le_pow₀ one_le_two) (by positivity) (by positivity) hyy' hd
    have cs := lintegral_mul_le_of_sq (ν.restrict (Q (i, i', a, b))) A B hA
      (Real.sqrt K * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (a + 1)) ^ kk *
        (((2 : ℝ) ^ i) ^ (24 * r ^ 3 + 1))⁻¹))
      (Real.sqrt K' * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (b + 1)) ^ kk *
        (((2 : ℝ) ^ i') ^ (24 * r ^ 3 + 1))⁻¹)) (by positivity) (by positivity)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h1 i i' (T i i' / 2 ^ (a + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, q2, q3, -, ⟨q4, q5⟩, -⟩
          exact ⟨q1, q2, q3, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K), Real.sq_sqrt hK.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (a + 1) = y
          generalize (2 : ℝ) ^ i = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h2 i i' (T i i' / 2 ^ (b + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, -, q2, q3, -, ⟨q4, q5⟩⟩
          exact ⟨q2, q3, q1, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K'), Real.sq_sqrt hK'.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (b + 1) = y
          generalize (2 : ℝ) ^ i' = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
    refine cs.trans ?_
    have e : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 ^ n)⁻¹) := fun n => by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.inv_pow]
      simp
    rw [e, e, e, e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_mul_mul_comm, ← Real.sqrt_mul hK.le, hC, mul_assoc (Real.sqrt (K * K'))]
    refine mul_le_mul_of_nonneg_left (key.trans ?_) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_assoc, mul_assoc]
    gcongr <;> simp
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν
      = ∫⁻ x in ⋃ p, Q p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' p, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal C * 16 := tsum_four _
    _ = ENNReal.ofReal (C * 16) := by rw [ENNReal.ofReal_mul hC0]; simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C * 16 ≤ C * 24 := by gcongr; norm_num
          _ = _ := by rw [hC]; ring
end GlobalTheory.Dyadic
