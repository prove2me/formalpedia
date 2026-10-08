-- Prove2me | solution 1 for OAI.Erdos3.affine_parameter_bad_pair_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:42:16.865246+00:00
-- url     : https://prove2.me/submissions/06b7d754-8abe-4726-94cb-6fc847c1471e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem reciprocal_square_le_reciprocal_difference {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      one_div_le_one_div_of_le (mul_pos hnR hp) (by nlinarith)
    _ = _ := by field_simp; ring

theorem finite_shifted_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N ≤ n) :
    (∑ n ∈ S, 1 / ((n : ℝ) + 1) ^ 2) ≤ 1 / (N : ℝ) := by
  let B := max N (S.sup id + 1)
  have hNB : N ≤ B := Nat.le_max_left _ _
  have hsub : S ⊆ Finset.Ico N B := by
    intro n hn
    apply Finset.mem_Ico.mpr
    exact ⟨hS n hn, (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)).trans_le (Nat.le_max_right _ _)⟩
  have htel : (∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
      1 / (N : ℝ) - 1 / (B : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_sub_neg] using
      Finset.sum_Ico_sub (fun n : ℕ => -(1 / (n : ℝ))) hNB
  calc
    _ ≤ ∑ n ∈ Finset.Ico N B, 1 / ((n : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_square_le_reciprocal_difference (hN.trans_le (Finset.mem_Ico.mp hn).1)
    _ = 1 / (N : ℝ) - 1 / (B : ℝ) := htel
    _ ≤ 1 / (N : ℝ) := sub_le_self _ (by positivity)

theorem finite_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N < n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  have hinj : Set.InjOn (fun n : ℕ => n - 1) S := by
    intro n hn m hm h
    change n - 1 = m - 1 at h
    have hn' := hS n hn
    have hm' := hS m hm
    omega
  have hshift : (∑ n ∈ S.image (fun n : ℕ => (n - 1 : ℕ)), 1 / ((n : ℝ) + 1) ^ 2) =
      ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have heq : n - 1 + 1 = n := by have h := hS n hn; omega
    have hr : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast heq
    rw [hr]
  rw [← hshift]
  apply finite_shifted_reciprocal_square_tail _ hN
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have h := hS m hm
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_reciprocal_power_tail (S : Finset ℕ) {N k : ℕ} (hN : 0 < N)
    (hk : 2 ≤ k) (hS : ∀ n ∈ S, N < n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ k) ≤ 1 / (N : ℝ) ^ (k - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : k = 2 + (k - 2) := by omega
  have hsplit' : k - 1 = 1 + (k - 2) := by omega
  calc
    _ ≤ ∑ n ∈ S, (1 / (N : ℝ) ^ (k - 2)) * (1 / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0 : ℝ) < n := hNR.trans (by exact_mod_cast hS n hn)
      have hp : (N : ℝ) ^ (k - 2) ≤ (n : ℝ) ^ (k - 2) :=
        pow_le_pow_left₀ hNR.le (by exact_mod_cast (hS n hn).le) _
      have hi := one_div_le_one_div_of_le (pow_pos hNR _) hp
      calc
        _ = (1 / (n : ℝ) ^ (k - 2)) * (1 / (n : ℝ) ^ 2) := by
          nth_rw 1 [hsplit]
          rw [pow_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = (1 / (N : ℝ) ^ (k - 2)) * ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / (N : ℝ) ^ (k - 2)) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail S hN hS) (by positivity)
    _ = _ := by rw [hsplit', pow_add, pow_one]; ring

theorem finite_divisor_error_tail (S : Finset ℕ) {N k : ℕ} (hN : 0 < N)
    (hk : 2 ≤ k) (hS : ∀ n ∈ S, N < n) {L : ℝ} (hL : 0 < L) :
    (∑ n ∈ S, (1 / (n : ℝ) + 1 / L) ^ k) ≤
      2 ^ (k - 1) * (1 / (N : ℝ) ^ (k - 1) + (S.card : ℝ) / L ^ k) := by
  calc
    _ ≤ ∑ n ∈ S, (2 : ℝ) ^ (k - 1) * (1 / (n : ℝ) ^ k + 1 / L ^ k) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [one_div_pow] using
        (add_pow_le (by positivity : 0 ≤ 1 / (n : ℝ)) (by positivity : 0 ≤ 1 / L) k)
    _ = 2 ^ (k - 1) * ((∑ n ∈ S, 1 / (n : ℝ) ^ k) + (S.card : ℝ) / L ^ k) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (finite_reciprocal_power_tail S hN hk hS) le_rfl) (by positivity)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

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

section

namespace Erdos3

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

section

namespace Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

theorem eventProbability_mono {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E F : Ω → Prop) (hEF : ∀ x, E x → F x) : p.eventProbability E ≤ p.eventProbability F := by
  classical
  apply p.mean_mono
  intro x
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · simp only [hE, ite_false]
    split_ifs <;> norm_num

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerBoxCharacterBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerInterval_indicator_expect (a b : ℤ) (hab : a ≤ b) (E : ℤ → Prop)
    [DecidablePred E] :
    (𝔼 x : Finset.Ico a b, if E x then (1 : ℝ) else 0) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (Finset.Ico a b) (fun x : ℤ => if E x then (1 : ℝ) else 0),
    Fintype.card_coe]
  have hcard : ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  rw [hcard]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

variable [MeasurableSpace C]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_mean (a b : ℤ) (hab : a < b) (f : Finset.Ico a b → ℝ) :
    (intervalUniformWeights a b hab).mean f = 𝔼 x, f x := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  unfold intervalUniformWeights
  exact FiniteProbabilityWeights.uniform_mean f

theorem interval_mod_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => (x : ℤ) ≡ v [ZMOD m]) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean,
    @integerInterval_indicator_expect a b hab.le (fun x : ℤ => x ≡ v [ZMOD m])
      (fun _ => Classical.propDecidable _)]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : (((b - a : ℤ) : ℝ) / (m : ℝ) + 1) / ((b - a : ℤ) : ℝ) =
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
    field_simp
  have hdiv := div_le_div_of_nonneg_right
    (scalarResidue_card_real_le a b m v hab.le hm) hL.le
  refine le_of_eq_of_le ?_ (hdiv.trans_eq heq)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  congr 2
  apply congrArg Finset.card
  ext x
  simp

theorem interval_divisor_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => m ∣ (x : ℤ) - v) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have heq : (fun x : Finset.Ico a b => m ∣ (x : ℤ) - v) =
      (fun x : Finset.Ico a b => (x : ℤ) ≡ v [ZMOD m]) := by
    funext x
    exact propext (by rw [Int.modEq_iff_dvd, dvd_sub_comm])
  rw [heq]
  exact interval_mod_probability a b m v hab hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxPairDivisibility
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_box_divisor_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (m : ℤ) (hm : 0 < m) (v : J → ℤ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
        (fun y => ∀ j, m ∣ (y j : ℤ) - v j) ≤
      ∏ j, (1 / (m : ℝ) + 1 / ((hi j - lo j : ℤ) : ℝ)) := by
  rw [integerBoxUniformWeights, FiniteProbabilityWeights.eventProbability_pi
    (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))
    (fun j (y : Finset.Ico (lo j) (hi j)) => m ∣ (y : ℤ) - v j)]
  apply Finset.prod_le_prod
  · intro j _
    exact FiniteProbabilityWeights.eventProbability_nonneg _ _
  · intro j _
    exact interval_divisor_probability (lo j) (hi j) m (v j) (hlen j) hm

theorem integer_box_pair_divisor_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (m : ℤ) (hm : 0 < m) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, m ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      ∏ j, (1 / (m : ℝ) + 1 / ((hi j - lo j : ℤ) : ℝ)) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (FiniteProbabilityWeights.mean_mono _ ?_).trans_eq (FiniteProbabilityWeights.mean_const _ _)
  intro x
  exact integer_box_divisor_probability lo hi hlen m hm (fun j => (x j : ℤ))

theorem integer_box_pair_divisor_probability_of_lengths {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (m : ℤ) (hm : 0 < m) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, m ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      (1 / (m : ℝ) + 1 / L) ^ Fintype.card J := by
  apply (integer_box_pair_divisor_probability lo hi hlen m hm).trans
  calc
    _ ≤ ∏ _j : J, (1 / (m : ℝ) + 1 / L) := by
      apply Finset.prod_le_prod
      · intro j _
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hj : (0 : ℝ) < ((hi j - lo j : ℤ) : ℝ) := hL.trans_le (hside j)
        positivity
      · intro j _
        exact add_le_add le_rfl (one_div_le_one_div_of_le hL (hside j))
    _ = _ := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LargeDivisorPairProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_box_pair_large_divisor_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  let p := (integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)
  have hunion := p.eventProbability_union_bound
    (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ))
    (fun (m : Finset.Ioc B R) xy => ∀ j, (m.val : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ))
    (by intro xy h; obtain ⟨m, hm, hd⟩ := h; exact ⟨⟨m, hm⟩, hd⟩)
  have hsum : p.eventProbability
      (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      ∑ m ∈ Finset.Ioc B R, (1 / (m : ℝ) + 1 / L) ^ Fintype.card J := by
    apply hunion.trans
    calc
      _ ≤ ∑ m : Finset.Ioc B R, (1 / (m.val : ℝ) + 1 / L) ^ Fintype.card J := by
        apply Finset.sum_le_sum
        intro m _
        have hm : 0 < m.val := hB.trans (Finset.mem_Ioc.mp m.property).1
        simpa only [p, Int.cast_natCast] using integer_box_pair_divisor_probability_of_lengths lo hi hlen
          (m.val : ℤ) (by exact_mod_cast hm) hL hside
      _ = _ := Finset.sum_coe_sort (Finset.Ioc B R)
        (fun m : ℕ => (1 / (m : ℝ) + 1 / L) ^ Fintype.card J)
  have htail := finite_divisor_error_tail (Finset.Ioc B R) hB hdim
    (fun m hm => (Finset.mem_Ioc.mp hm).1) hL
  have hcard : ((Finset.Ioc B R).card : ℝ) ≤ R := by
    exact_mod_cast (show (Finset.Ioc B R).card ≤ R by simp)
  apply hsum.trans (htail.trans _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hcard (by positivity))

theorem nonzero_common_divisor_bounded {J : Type*} (z : J → ℤ) (hz : z ≠ 0)
    {R m : ℕ} (hR : ∀ j, (z j).natAbs ≤ R) (hdiv : ∀ j, (m : ℤ) ∣ z j) : m ≤ R := by
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have h := (Int.natAbs_le_of_dvd_ne_zero (hdiv j) hj).trans (hR j)
  simpa using h

theorem integer_box_pair_nonzero_large_divisor_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => xy.1 ≠ xy.2 ∧
          ∃ m : ℕ, B < m ∧ ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_large_divisor_probability lo hi hlen B R hB hdim hL hside)
  intro xy hxy
  obtain ⟨hne, m, hm, hd⟩ := hxy
  have hz : (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≠ 0 := by
    intro he
    apply hne
    funext j
    apply Subtype.ext
    have hj := congrFun he j
    change (xy.2 j : ℤ) - (xy.1 j : ℤ) = 0 at hj
    omega
  have hR : ∀ j, ((xy.2 j : ℤ) - (xy.1 j : ℤ)).natAbs ≤ R := by
    intro j
    have hx := Finset.mem_Ico.mp (xy.1 j).property
    have hy := Finset.mem_Ico.mp (xy.2 j).property
    have hw := hwidth j
    have habs : |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (R : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have hc : (((xy.2 j : ℤ) - (xy.1 j : ℤ)).natAbs : ℤ) ≤ R := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hc
  exact ⟨m, Finset.mem_Ioc.mpr ⟨hm, nonzero_common_divisor_bounded _ hz hR hd⟩, hd⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem interval_event_probability (a b : ℤ) (hab : a < b) (E : ℤ → Prop)
    [DecidablePred E] :
    (intervalUniformWeights a b hab).eventProbability (fun x => E (x : ℤ)) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean]
  convert integerInterval_indicator_expect a b hab.le E using 1
  congr 1
  funext x
  split_ifs <;> rfl

theorem interval_near_probability (a b v : ℤ) (hab : a < b) (r : ℕ) :
    (intervalUniformWeights a b hab).eventProbability (fun x => |(x : ℤ) - v| ≤ (r : ℤ)) ≤
      (2 * (r : ℝ) + 1) / ((b - a : ℤ) : ℝ) := by
  rw [interval_event_probability a b hab (fun x => |x - v| ≤ (r : ℤ))]
  have hsub : (Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)) ⊆
      Finset.Icc (v - (r : ℤ)) (v + (r : ℤ)) := by
    intro x hx
    have h := abs_le.mp (Finset.mem_filter.mp hx).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have he : (Finset.Icc (v - (r : ℤ)) (v + (r : ℤ))).card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hc : ((Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)).card : ℝ) ≤
      2 * (r : ℝ) + 1 := by
    have h := Finset.card_le_card hsub
    rw [he] at h
    exact_mod_cast h
  exact div_le_div_of_nonneg_right hc (by exact_mod_cast (sub_pos.mpr hab).le)

theorem integer_box_near_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (v : J → ℤ) (r : ℕ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
        (fun y => ∀ j, |(y j : ℤ) - v j| ≤ (r : ℤ)) ≤
      ∏ j, (2 * (r : ℝ) + 1) / ((hi j - lo j : ℤ) : ℝ) := by
  rw [integerBoxUniformWeights, FiniteProbabilityWeights.eventProbability_pi
    (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))
    (fun j (y : Finset.Ico (lo j) (hi j)) => |(y : ℤ) - v j| ≤ (r : ℤ))]
  apply Finset.prod_le_prod
  · intro j _
    exact FiniteProbabilityWeights.eventProbability_nonneg _ _
  · intro j _
    exact interval_near_probability (lo j) (hi j) (v j) (hlen j) r

theorem integer_box_pair_near_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (r : ℕ) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (r : ℤ)) ≤
      ∏ j, (2 * (r : ℝ) + 1) / ((hi j - lo j : ℤ) : ℝ) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (FiniteProbabilityWeights.mean_mono _ ?_).trans_eq (FiniteProbabilityWeights.mean_const _ _)
  intro x
  exact integer_box_near_probability lo hi hlen (fun j => (x j : ℤ)) r

theorem integer_box_pair_near_probability_of_lengths {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (r : ℕ) {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (r : ℤ)) ≤
      ((2 * (r : ℝ) + 1) / L) ^ Fintype.card J := by
  apply (integer_box_pair_near_probability lo hi hlen r).trans
  calc
    _ ≤ ∏ _j : J, (2 * (r : ℝ) + 1) / L := by
      apply Finset.prod_le_prod
      · intro j _
        have hj : (0 : ℝ) < ((hi j - lo j : ℤ) : ℝ) := hL.trans_le (hside j)
        positivity
      · intro j _
        exact div_le_div_of_nonneg_left (by positivity) hL (hside j)
    _ = _ := by simp [div_pow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_vector_content_natAbs_scale {J : Type*} [Fintype J]
    (D : ℕ) (z : J → ℤ) :
    (BohrLattice.Primitive.content (fun j => (D : ℤ) * z j)).natAbs =
      D * (BohrLattice.Primitive.content z).natAbs := by
  simp only [BohrLattice.Primitive.content, Finset.gcd_mul_left, Int.normalize_coe_nat,
    Int.natAbs_mul, Int.natAbs_natCast]

theorem affine_parameter_difference_gcd {J : Type*} [Fintype J]
    (D : ℕ) (a x y : J → ℤ) :
    (BohrLattice.Primitive.content (fun j => (a j + (D : ℤ) * y j) -
      (a j + (D : ℤ) * x j))).natAbs =
      D * (BohrLattice.Primitive.content (fun j => y j - x j)).natAbs := by
  have he : (fun j => (a j + (D : ℤ) * y j) - (a j + (D : ℤ) * x j)) =
      (fun j => (D : ℤ) * (y j - x j)) := by funext j; ring
  rw [he, integer_vector_content_natAbs_scale]

theorem integer_box_pair_gcd_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => B < (BohrLattice.Primitive.content
          (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ))).natAbs) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_nonzero_large_divisor_probability lo hi hlen B R hB hdim hL hside hwidth)
  intro xy h
  refine ⟨?_, (BohrLattice.Primitive.content (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ))).natAbs, h, ?_⟩
  · intro he
    have hz : Finset.univ.gcd (fun _ : J => (0 : ℤ)) = 0 :=
      Finset.gcd_eq_zero_iff.mpr (fun _ _ => rfl)
    simp [he, BohrLattice.Primitive.content, hz] at h
  · intro j
    exact Int.natAbs_dvd.mpr (BohrLattice.Primitive.content_dvd _ j)

theorem affine_parameter_pair_gcd_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => Q < (BohrLattice.Primitive.content
          (fun j => (a j + (D : ℤ) * (xy.2 j : ℤ)) -
            (a j + (D : ℤ) * (xy.1 j : ℤ)))).natAbs) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_gcd_probability lo hi hlen B R hB hdim hL hside hwidth)
  intro xy h
  rw [affine_parameter_difference_gcd] at h
  exact Nat.lt_of_mul_lt_mul_left (hBQ.trans_lt h)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_event_probability_or_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (A B : X → Prop) :
    p.eventProbability (fun x => A x ∨ B x) ≤ p.eventProbability A + p.eventProbability B := by
  have hpoint (x : X) : (@ite ℝ (A x ∨ B x) (Classical.propDecidable _) 1 0) ≤
      (@ite ℝ (A x) (Classical.propDecidable _) 1 0) +
      (@ite ℝ (B x) (Classical.propDecidable _) 1 0) := by
    by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]
  exact (p.mean_mono hpoint).trans_eq (p.mean_add _ _)

theorem affine_parameter_bad_pair_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R r : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
      (fun xy => affineParameterBadPair D Q r a
        (fun j => (xy.1 j : ℤ)) (fun j => (xy.2 j : ℤ))) ≤
      integerBoxBadPairBudget (Fintype.card J) B R r L := by
  unfold affineParameterBadPair integerBoxBadPairBudget
  apply (finite_event_probability_or_le _ _ _).trans
  exact add_le_add
    (affine_parameter_pair_gcd_probability lo hi hlen D Q B R a hBQ hB hdim hL hside hwidth)
    (integer_box_pair_near_probability_of_lengths lo hi hlen r hL hside)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

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

theorem solution.{u_1} : type_of% @OAI.Erdos3.affine_parameter_bad_pair_probability.{u_1} := @OAI.Erdos3.affine_parameter_bad_pair_probability.{u_1}
