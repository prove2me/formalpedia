-- Prove2me | solution 1 for OAI.Erdos3.allocated_weighted_physical_replacement_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:13:17.780431+00:00
-- url     : https://prove2.me/submissions/dbc61118-7198-47d2-b369-f74a38840209

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_physicalBoxResidual_control_of_lengths_s2
import Theorems.Thm_OAI_Erdos3_retained_physical_residual_correlation_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem residual_three_term_budget {M K F T S cap V eta delta rho epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hF : 0 ≤ F) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hcap : 0 ≤ cap) (hV : cap ≤ V) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (henergy : eta * V ^ 2 ≤ 1)
    (hcancel : 3 * M * K * eta * V ^ 2 ≤ epsilon)
    (hpoint : 6 * M * S * F * delta ≤ epsilon) (hgrid : 6 * M * S * T * rho ≤ epsilon) :
    M * (K * (eta * cap) ^ 2 + (F * delta + T * rho) * S * (1 + eta * cap ^ 2)) ≤ epsilon := by
  have hsq : cap ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hcap hV 2
  have hmean : eta * cap ^ 2 ≤ eta * V ^ 2 := mul_le_mul_of_nonneg_left hsq heta
  have hcancel' : (eta * cap) ^ 2 ≤ eta * V ^ 2 := by
    calc
      _ = eta * (eta * cap ^ 2) := by ring
      _ ≤ 1 * (eta * cap ^ 2) := mul_le_mul_of_nonneg_right heta1 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hmean
  calc
    _ ≤ M * (K * (eta * V ^ 2) + (F * delta + T * rho) * S * 2) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply add_le_add (mul_le_mul_of_nonneg_left hcancel' hK)
      apply mul_le_mul_of_nonneg_left (by linarith : 1 + eta * cap ^ 2 ≤ 2)
      positivity
    _ = M * K * eta * V ^ 2 + 2 * M * S * F * delta + 2 * M * S * T * rho := by ring
    _ ≤ epsilon := by nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_base_cap {K I X Y : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) (f : (Option K × I → X) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) (hp : ∀ i x, (p (none,i) x).toReal ≤ C i) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ ∏ i, C i := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp_rw [PMF.map_comp]
  apply pmf_bind_injective_toReal_cap _ _ _ hf (Finset.prod_nonneg (fun i _ => hC i))
  intro base
  rw [independentProductPMF_toReal]
  exact Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hp i (base i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_finite_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℝ) :
    (∑' x, (p x).toReal * φ (F x)) = ∑ y ∈ T, (p.map F y).toReal * φ y := by
  have hs : (∑' x, (p x).toReal * φ (F x)) = ∑ x ∈ S, (p x).toReal * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_energy_of_point_cap {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (e : Y → ℝ) (he : ∀ y ∉ T, e y = 0)
    {C : ℝ} (hcap : ∀ y, (p.map F y).toReal ≤ C) :
    (∑' x, (p x).toReal * e (F x) ^ 2) ≤ C * ∑ y ∈ T, e y ^ 2 := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hsum : (∑ y ∈ U, e y ^ 2) = ∑ y ∈ T, e y ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [he y hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [pmf_image_finite_real_mean p S hp F U hU (fun y => e y ^ 2)]
  calc
    _ ≤ ∑ y ∈ U, C * e y ^ 2 :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcap y) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductPMF_base_cap {K I Y : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (Option K × I → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S (none,i)) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ ∏ i, 2 / S (none,i) := by
  rw [shiftedSmoothProductPMF_eq_independent]
  apply independentProductPMF_base_cap _ f hf (fun i => 2 / S (none,i))
    (fun i => div_nonneg (by norm_num) (hS (none,i)).le)
  intro i k
  exact shiftedSmoothCoefficientPMF_le (a (none,i)) (hbase i) k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

theorem shiftedSmoothCoefficientPMF_inner_lower (a : ℝ) {S : ℝ}
    (hscale : 8 * (probabilityProfileLipschitz : ℝ) ≤ S)
    (hS : 0 < S) (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ)
    (hk : |(k : ℝ) - a| ≤ S / 2) :
    1 / (3 * S) ≤ (shiftedSmoothCoefficientPMF a S hS hZ k).toReal := by
  have hk' : |((k : ℝ) - a) / S| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hS]
    exact (div_le_iff₀ hS).mpr (by linarith)
  rw [shiftedSmoothCoefficientPMF_apply]
  have hp := smoothProbabilityProfile_inner_lower _ hk'
  have hb := (shiftedSmoothSampleSum_bounds a hscale).2
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * S) hZ).mpr
  nlinarith

theorem shiftedSmoothProductPMF_inner_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    (∏ i, 1 / (3 * S i)) ≤ (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (hS i).le)
  · intro i _
    exact shiftedSmoothCoefficientPMF_inner_lower (a i) (hscale i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i) (z i) (hz i)

theorem shiftedSmoothProductPMF_inner_mass {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    1 ≤ (∏ i, 3 * S i) * (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  have hprod : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := shiftedSmoothProductPMF_inner_lower a S hS hZ hscale z hz
  rw [Finset.prod_div_distrib] at h
  simp only [Finset.prod_const_one] at h
  exact (div_le_iff₀ hprod).mp h |>.trans_eq (mul_comm _ _)

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_energy_aggregate {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (e : X → ℝ) {E : ℝ}
    (he : ∀ a, finiteCellMean p C (fun x => e x ^ 2) a ≤ E * (finiteCellWeights p C).weight a) :
    p.mean (fun x => e x ^ 2) ≤ E := by
  rw [← finiteCellMean_sum p C]
  calc
    _ ≤ ∑ a, E * (finiteCellWeights p C).weight a := Finset.sum_le_sum (fun a _ => he a)
    _ = E := by rw [← Finset.mul_sum, (finiteCellWeights p C).total, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_uniform {X A : Type*} [Fintype X] [Nonempty X] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X *
        (𝔼 x : {x // C x = a}, f x.val) :=
  uniform_subtype_mean (fun x => C x = a) f

theorem finiteCellWeights_uniform {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (a : A) :
    (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X := by
  change finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun _ => 1) a = _
  rw [finiteCellMean_uniform]
  by_cases h : Nonempty {x // C x = a}
  · let : Nonempty {x // C x = a} := h
    simp
  · let : IsEmpty {x // C x = a} := not_nonempty_iff.mp h
    simp

theorem finiteCellMean_uniform_weighted {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, f x.val) := by
  rw [finiteCellWeights_uniform, finiteCellMean_uniform]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem smoothAffineSample_base_injective {K I : Type*} [Fintype K]
    (t : K → ℤ) (tail : K × I → ℤ) :
    Function.Injective (fun base => smoothAffineSample t (baseArrayJoin tail base)) := by
  intro b c h
  funext i
  have hi := congrFun h i
  change b i + (∑ k, t k * tail (k, i)) = c i + (∑ k, t k * tail (k, i)) at hi
  exact add_right_cancel hi

theorem smoothAffineSample_point_cap {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (y : I → ℤ) :
    ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffineSample t) y).toReal ≤
      ∏ i, 2 / S (none, i) :=
  shiftedSmoothProductPMF_base_cap a S hS hZ (smoothAffineSample t)
    (smoothAffineSample_base_injective t) hbase y

theorem smoothAffineSample_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * ∑ y ∈ T, e y ^ 2 :=
  pmf_image_energy_of_point_cap (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) T e he (smoothAffineSample_point_cap a S hS hZ hbase t)

theorem smoothAffineSample_energy_of_sum_bound {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  exact (smoothAffineSample_energy a S hS hZ hbase t T e he).trans
    (mul_le_mul_of_nonneg_left henergy (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_window_change_of_measure {X : Type*} [DecidableEq X]
    (S W : Finset X) (hWS : W ⊆ S) (p : FiniteProbabilityWeights S)
    {D : ℝ} (hD : 0 < D)
    (hlower : ∀ z : S, z.val ∈ W → 1 ≤ D * p.weight z) :
    ∃ w : S → ℝ, (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : X → ℝ, (𝔼 z ∈ W, f z) =
        (D / W.card) * p.mean (fun z => w z * f z.val) := by
  let w : S → ℝ := fun z => if z.val ∈ W then 1 / (D * p.weight z) else 0
  have hw (z : S) : 0 ≤ w z ∧ w z ≤ 1 := by
    dsimp only [w]
    split_ifs with hz
    · have hpos : 0 < D * p.weight z := lt_of_lt_of_le zero_lt_one (hlower z hz)
      exact ⟨div_nonneg zero_le_one hpos.le, (div_le_one hpos).mpr (hlower z hz)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  refine ⟨w, hw, fun f => ?_⟩
  have hpoint (z : S) : D * (p.weight z * (w z * f z.val)) =
      if z.val ∈ W then f z.val else 0 := by
    by_cases hz : z.val ∈ W
    · have hp : p.weight z ≠ 0 := by
        intro h
        have hh := hlower z hz
        norm_num [h] at hh
      simp only [w, hz, ite_true]
      field_simp
    · simp [w, hz]
  have hsum : D * p.mean (fun z => w z * f z.val) = ∑ z ∈ W, f z := by
    unfold FiniteProbabilityWeights.mean
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_coe_sort S (fun z => if z ∈ W then f z else 0)]
    calc
      _ = ∑ z ∈ W, if z ∈ W then f z else 0 :=
        (Finset.sum_subset hWS (fun z _ hz => by simp [hz])).symm
      _ = _ := Finset.sum_congr rfl (fun z hz => by simp [hz])
  rw [Finset.expect_eq_sum_div_card, ← hsum]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSourceFiniteWeights_mean {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (J → ℤ) → ℝ) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => f z.val) =
      ∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * f z := by
  unfold FiniteProbabilityWeights.mean
  change (∑ z : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ z.val).toReal * f z.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal * f z)]
  exact (hasSum_sum_of_ne_finset_zero (fun z hz => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hz, zero_mul])).tsum_eq.symm

theorem smoothSourceFiniteWeights_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => e (smoothAffineSample t z.val) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  rw [smoothSourceFiniteWeights_mean a S hS hZ (fun z => e (smoothAffineSample t z) ^ 2)]
  exact smoothAffineSample_energy_of_sum_bound a S hS hZ hbase t T e he henergy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smooth_inner_mem_indices {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    z ∈ rectangularWeightIndices a S 1 := by
  classical
  by_contra hn
  have h := shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z hz
  rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hn, mul_zero] at h
  norm_num at h

theorem smooth_window_change_of_measure {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (I → ℤ)) (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    ∃ w : rectangularWeightIndices a S 1 → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : (I → ℤ) → ℝ, (𝔼 z ∈ W, f z) =
        ((3 : ℝ) ^ Fintype.card I * (∏ i, S i) / W.card) *
          (smoothSourceFiniteWeights a S hS hZ).mean (fun z => w z * f z.val) := by
  classical
  have hsub : W ⊆ rectangularWeightIndices a S 1 :=
    fun z hz => smooth_inner_mem_indices a S hS hZ hscale z (hW z hz)
  have hD : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := finite_window_change_of_measure (rectangularWeightIndices a S 1) W hsub
    (smoothSourceFiniteWeights a S hS hZ) hD
    (fun z hz => shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z.val (hW z.val hz))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

theorem shiftedSmoothProductMass_pos_of_large_scales {I : Type*} [Fintype I]
    (a S : I → ℝ) (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hscale i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hscale i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSmoothSampledError
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_mean_square_as_pair {T : Type*} [Fintype T]
    (q : FiniteProbabilityWeights T) (f : T → ℝ) :
    (q.mean f) ^ 2 = (q.prod q).mean (fun t => f t.1 * f t.2) := by
  rw [FiniteProbabilityWeights.mean_prod]
  simp only [q.mean_const_mul, q.mean_mul_const, pow_two]

theorem sampled_second_moment_identity {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ) :
    p.mean (fun x => (q.mean (e x)) ^ 2) =
      (q.prod q).mean (fun t => p.mean (fun x => e x t.1 * e x t.2)) := by
  simp_rw [finite_mean_square_as_pair q]
  exact p.mean_comm (q.prod q) (fun x t => e x t.1 * e x t.2)

theorem finite_mean_bad_event_bound {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Bad : X → Prop) (f : X → ℝ) {C epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbad : ∀ x, Bad x → f x ≤ C)
    (hgood : ∀ x, ¬ Bad x → f x ≤ epsilon) :
    p.mean f ≤ C * p.eventProbability Bad + epsilon := by
  have hpoint (x : X) : f x ≤ C * (if Bad x then (1 : ℝ) else 0) + epsilon := by
    by_cases hx : Bad x
    · simp only [hx, ite_true, mul_one]
      linarith [hbad x hx]
    · simpa only [hx, ite_false, mul_zero, zero_add] using hgood x hx
  apply (p.mean_mono hpoint).trans_eq
  rw [p.mean_add, p.mean_const_mul, p.mean_const]
  rfl

theorem sampled_second_moment_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon) :
    p.mean (fun x => (q.mean (e x)) ^ 2) ≤ C * beta + epsilon := by
  rw [sampled_second_moment_identity]
  have h := finite_mean_bad_event_bound (q.prod q) Bad
    (fun t => p.mean (fun x => e x t.1 * e x t.2)) hepsilon
    (fun t ht => (le_abs_self _).trans (hbad t ht))
    (fun t ht => (le_abs_self _).trans (hgood t ht))
  have hm := mul_le_mul_of_nonneg_left hmass hC
  linarith

theorem sampled_weighted_error_of_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) := by
  have he := sampled_second_moment_bad_pairs p q e Bad hC hepsilon hmass hbad hgood
  have hw2 : p.mean (fun x => w x ^ 2) ≤ 1 := by
    apply (p.mean_mono (g := fun _ => 1) ?_).trans_eq (p.mean_const 1)
    intro x
    have h := hw x
    nlinarith
  have he0 := p.mean_nonneg (fun x => sq_nonneg (q.mean (e x)))
  have hc := p.mean_mul_sq_le w (fun x => q.mean (e x))
  have hm := mul_le_mul_of_nonneg_right hw2 he0
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  nlinarith only [hc, hm, he]

theorem sampled_pair_correlation_cap {Ω T : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (e : Ω → T → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C) (t u : T) :
    |p.mean (fun x => e x t * e x u)| ≤ C := by
  apply abs_le_of_sq_le_sq _ hC
  calc
    _ ≤ p.mean (fun x => e x t ^ 2) * p.mean (fun x => e x u ^ 2) :=
      p.mean_mul_sq_le (fun x => e x t) (fun x => e x u)
    _ ≤ C * C := mul_le_mul (henergy t) (henergy u) (p.mean_nonneg (fun x => sq_nonneg _)) hC
    _ = C ^ 2 := by ring

theorem sampled_weighted_error_of_energy {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) :=
  sampled_weighted_error_of_bad_pairs p q e Bad hC hepsilon hmass
    (fun t _ => sampled_pair_correlation_cap p e hC henergy t.1 t.2) hgood w hw

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smooth_window_weighted_sampled_error {K I P : Type*}
    [Fintype K] [Fintype I] [Fintype P]
    (a S : Option K × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (Option K × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2)
    (q : FiniteProbabilityWeights P) (t : P → K → ℤ)
    (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E epsilon beta : ℝ} (hE : 0 ≤ E) (hepsilon : 0 ≤ epsilon)
    (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card)
    (Bad : P × P → Prop) (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ u, ¬ Bad u → |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample (t u.1) z.val) * e (smoothAffineSample (t u.2) z.val))| ≤ epsilon)
    (v : (Option K × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    |𝔼 z ∈ W, v z * q.mean (fun u => e (smoothAffineSample (t u) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card) *
        Real.sqrt (((∏ i, 2 / S (none, i)) * (E * T.card)) * beta + epsilon) := by
  obtain ⟨w, hw, hchange⟩ := smooth_window_change_of_measure a S hS hZ hscale W hW
  have hC : 0 ≤ (∏ i, 2 / S (none, i)) * (E * T.card) := by
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le))
      (mul_nonneg hE (Nat.cast_nonneg _))
  have hprod (z : rectangularWeightIndices a S 1) : 0 ≤ w z * v z.val ∧ w z * v z.val ≤ 1 :=
    ⟨mul_nonneg (hw z).1 (hv z.val).1,
      (mul_le_mul (hw z).2 (hv z.val).2 (hv z.val).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsample := sampled_weighted_error_of_energy (smoothSourceFiniteWeights a S hS hZ) q
    (fun z u => e (smoothAffineSample (t u) z.val)) Bad hC hepsilon
    (fun u => smoothSourceFiniteWeights_energy a S hS hZ (fun i => hscale (none, i)) (t u) T e he henergy)
    hmass hgood (fun z => w z * v z.val) hprod
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card := by
    exact div_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hS i).le))) (Nat.cast_nonneg _)
  rw [hchange (fun z => v z * q.mean (fun u => e (smoothAffineSample (t u) z))), abs_mul, abs_of_nonneg hfactor]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsample) hfactor

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

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

theorem smoothPairProbabilityError_mul {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) :
    smoothPairProbabilityError k Q C κ δ = smoothPairProbabilityError k Q C κ 1 * δ := by
  simp only [smoothPairProbabilityError, mul_one]

theorem fullSmoothPairError_le_linear {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    fullSmoothPairError n k Q C κ δ ≤ smoothPairErrorCoefficient n k Q C κ * δ := by
  have hE := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hcap : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  have hEd : 0 ≤ smoothPairProbabilityError k Q C κ 1 * δ := mul_nonneg hE hδ
  have hle : smoothPairProbabilityError k Q C κ 1 * δ ≤ smoothPairProbabilityError k Q C κ 1 := by
    nlinarith
  unfold fullSmoothPairError smoothPairErrorCoefficient
  rw [smoothPairProbabilityError_mul k Q C κ δ]
  calc
    _ ≤ n * (smoothPairProbabilityError k Q C κ 1 * δ) *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg hcap hEd) (add_le_add le_rfl hle) n)
        (mul_nonneg (Nat.cast_nonneg _) hEd)
    _ = _ := by unfold fullSmoothPairError; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

theorem boundedPrimePower_pairwise (Q : ℕ) :
    Pairwise (fun p r : BoundedPrime Q => (boundedPrimePower Q p).Coprime (boundedPrimePower Q r)) := by
  intro p r hpr
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (boundedPrime_prime Q p) (boundedPrime_prime Q r)).mpr
    (fun h => hpr (Subtype.ext h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCellResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physical_cell_residual_energy {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val)) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => e x ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) * (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c := by
  have hmean := Fintype.expect_equiv E (fun x => e x.val ^ 2)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) ^ 2) (fun x => by rw [he x])
  rw [finiteCellMean_uniform_weighted, hmean]
  exact (mul_le_mul_of_nonneg_left hcontrol.2.1
    ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg c)).trans_eq (mul_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_zero_off (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : x ∉ translatedIntegerBox lo N) :
    physicalBoxResidual lo N P hpos q b f x = 0 := by
  simp only [physicalBoxResidual, if_neg hx]

theorem physicalBoxResidual_on_cell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (c : ∀ i, (P i).Label) (x : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c}) :
    physicalBoxResidual lo N P hpos q b f x.val.val = f x.val.val -
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x.val.val := by
  simp only [physicalBoxResidual, if_pos x.val.property,
    physicalBoxTruncation, dif_pos x.val.property]
  rw [x.property]

theorem physicalBoxResidual_cell_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    finiteCellMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) *
        (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c := by
  exact physical_cell_residual_energy (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c)

theorem physicalBoxResidual_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ)
    (hc : ∀ c : (∀ i, (P i).Label), ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)).mean
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) ≤
      1 + eta * residueTruncationCap ι b eta ^ 2 := by
  exact finite_cell_energy_aggregate (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N))
    (physicalBoxCell lo N P) (fun x => physicalBoxResidual lo N P hpos q b f x.val)
    (fun c => physicalBoxResidual_cell_energy lo N P hstep hpos q b f eta c (hc c))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  unfold residueTruncationCap
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_step {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    (normalizedBoxPartitions N H ρ hlarge hwhole i).step c = 1 := rfl

theorem normalizedBoxPartitions_lengths {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    ρ * H i / 4 ≤ ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ∧
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ≤ ρ * H i := by
  obtain ⟨_, _, hlo, hup⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
  have hl := comparableBoxPartitions_length N (fun j => ⌊ρ * H j / 2⌋₊)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).1)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).2.1) i c
  have hl' : (⌊ρ * H i / 2⌋₊ : ℝ) ≤
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) := by exact_mod_cast hl.1
  have hu' : ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) <
      2 * (⌊ρ * H i / 2⌋₊ : ℝ) := by exact_mod_cast hl.2
  exact ⟨hlo.trans hl', by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translated_box_volume_ratio {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) :
    (translatedIntegerBox lo N).card / (∏ i, H i) = ∏ i, (N i : ℝ) / H i := by
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod, Finset.prod_div_distrib]

theorem translated_box_volume_ratio_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    (translatedIntegerBox lo N).card / (∏ i, H i) ≤ A ^ Fintype.card I := by
  rw [translated_box_volume_ratio]
  calc
    _ ≤ ∏ _i : I, A := Finset.prod_le_prod
      (fun i _ => div_nonneg (Nat.cast_nonneg _) (hH i).le)
      (fun i _ => (div_le_iff₀ (hH i)).mpr (hside i))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

theorem translated_box_pair_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) ≤ A ^ (2 * Fintype.card I) := by
  rw [Finset.prod_pow, ← div_pow]
  have h := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hH i).le)))
    (translated_box_volume_ratio_le lo N H hH hside) 2
  simpa only [← pow_mul, Nat.mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

theorem residueTruncationCap_le_envelope (ι : Type*) [Fintype ι] [DecidableEq ι]
    (degree : ℕ) {eta : ℝ} (heta : eta ≤ 1) :
    residueTruncationCap ι degree eta ≤ residualCapEnvelope ι degree := by
  have h := mul_le_mul_of_nonneg_left (show 1 + eta ≤ 2 by linarith)
    (show 0 ≤ ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree by positivity)
  unfold residueTruncationCap residualCapEnvelope
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem physicalResidualPairBudget_nonneg {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (k : J) (Q : ℕ)
    (C κ δ : ℝ) (degree : ℕ) (eta ρ : ℝ) (hδ : 0 ≤ δ) (heta : 0 ≤ eta) (hρ : 0 ≤ ρ) :
    0 ≤ physicalResidualPairBudget lo N H k Q C κ δ degree eta ρ := by
  have he := fullSmoothPairError_nonneg (Fintype.card I) k Q C κ δ hδ
  unfold physicalResidualPairBudget
  positivity

end Erdos3

end

section

namespace Erdos3

theorem physicalResidualPairBudget_of_accuracies {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i) (k : J) (Q : ℕ)
    (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
    let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
    let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
    physicalResidualPairBudget lo N H k Q C κ delta degree eta rho ≤ epsilon := by
  let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
  let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
  let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
  have hd := physicalPairPointAccuracy_spec (Fintype.card I) k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec (Fintype.card I) k C κ hA heps
  have he := physicalPairMeanAccuracy_spec (Fintype.card I) k Q C κ degree hA heps
  have hd0 : 0 ≤ delta := hd.1.le
  have hr0 : 0 ≤ rho := hr.1.le
  have he0 : 0 ≤ eta := he.1.le
  have hfull := fullSmoothPairError_nonneg (Fintype.card I) k Q C κ delta hd0
  have hcap0 := residueTruncationCap_nonneg (BoundedPrime Q) degree he.1.le
  have hcap := residueTruncationCap_le_envelope (BoundedPrime Q) degree he.2.1
  have hM : 0 ≤ A ^ (2 * Fintype.card I) := by positivity
  have halloc := residual_three_term_budget hM (NNReal.coe_nonneg (smoothPairKernelCap (Fintype.card I) k C κ))
    (smoothPairErrorCoefficient_nonneg (Fintype.card I) k Q C κ)
    (NNReal.coe_nonneg (smoothPairKernelLip (Fintype.card I) k C κ))
    (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card I)
    hcap0 hcap he.1.le he.2.1 hd.1.le hr.1.le he.2.2.1 he.2.2.2 hd.2.2.1 hr.2.2
  have hpoint := fullSmoothPairError_le_linear (Fintype.card I) k Q C κ hd.1.le hd.2.1
  dsimp only
  unfold physicalResidualPairBudget
  apply le_trans _ halloc
  apply mul_le_mul (translated_box_pair_volume_le lo N H hH hside) _ (by positivity) hM
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact add_le_add hpoint le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_physical_residual_sum_energy {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (Q degree : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog accLog eta : ℝ) (hmodLog : 0 ≤ modLog) (heta : eta ≤ 1)
    (hacc : Real.exp (-accLog) ≤ eta) (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    (∑ x ∈ translatedIntegerBox lo N, physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f x ^ 2) ≤
      (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) * (translatedIntegerBox lo N).card := by
  let P := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  have hstep := normalizedBoxPartitions_step N H ρ hlarge hwhole
  have hN (i : I) : 0 < N i := by
    have h : (0 : ℝ) < N i := by linarith [hlarge i, hwhole i]
    exact_mod_cast h
  have hlo : lo ∈ translatedIntegerBox lo N := (mem_translatedIntegerBox lo N lo).mpr
    (fun i => ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hN i)⟩)
  let : Nonempty (translatedIntegerBox lo N) := ⟨⟨lo, hlo⟩⟩
  have hc (c : ∀ i, (P i).Label) := physicalBoxResidual_control_of_lengths_s2 lo N P hstep hpos
    (boundedPrimePower Q) (boundedPrimePower_pairwise Q) degree f hf modLog dimLog accLog eta hmodLog heta hacc
    (fun j => (Nat.cast_le.mpr (boundedPrimePower_le Q j)).trans hQlog) hdim
    (fun i c => (hlength i).trans (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).1) c
  have h := physicalBoxResidual_energy lo N P hstep hpos (boundedPrimePower Q) degree f eta hc
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort (translatedIntegerBox lo N)
      (fun x => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f x ^ 2)] at h
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨lo, hlo⟩))).mp h

end Erdos3

end

section

namespace Erdos3

theorem physicalMeanAccuracyLog_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ}
    (hA : 0 ≤ A) (heps : 0 < epsilon) :
    0 ≤ physicalMeanAccuracyLog n k Q C κ A degree epsilon ∧
      Real.exp (-physicalMeanAccuracyLog n k Q C κ A degree epsilon) =
        physicalPairMeanAccuracy n k Q C κ A degree epsilon := by
  have h := physicalPairMeanAccuracy_spec n k Q C κ degree hA heps
  constructor
  · have hl := Real.log_le_log h.1 h.2.1
    rw [Real.log_one] at hl
    exact neg_nonneg.mpr hl
  · simp only [physicalMeanAccuracyLog, neg_neg, Real.exp_log h.1]

theorem smoothPairCoefficientScale_large {I J : Type*} (H : I → ℝ) {L U : ℝ}
    (hL : 1 ≤ L) (hU : 0 ≤ U) (hH : ∀ i, U ≤ H i / L) :
    ∀ z : Option J × I, U ≤ smoothPairCoefficientScale (H z.2) L z.1 := by
  rintro ⟨j, i⟩
  cases j with
  | none =>
      exact (le_mul_of_one_le_right hU hL).trans ((le_div_iff₀ (zero_lt_one.trans_le hL)).mp (hH i))
  | some j => exact hH i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ)
    (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree)
    (B R : ℕ) (hBQ : D * B ≤ Q) (hB : 0 < B) (hparamDim : 2 ≤ Fintype.card J)
    (parMin : ℝ) (hparMin : 0 < parMin)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hscale : ∀ z : Option J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
      smoothPairCoefficientScale (H z.2) L z.1)
    (W : Finset (Option J × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2)
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option J × I) *
        (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card) *
      Real.sqrt (((∏ i, 2 / H i) * ((1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) *
        (translatedIntegerBox lo N).card)) * integerBoxBadPairBudget (Fintype.card J) B R r parMin +
        physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ) := by
  let P := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  let e : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
  have heta0 : 0 ≤ eta := (Real.exp_pos _).le.trans hacc
  have hepsilon := physicalResidualPairBudget_nonneg lo N H k0 Q C κ δ degree eta ρ hδ heta0 hρ
  have henergy := normalized_physical_residual_sum_energy lo N H ρ hlarge hwhole Q degree f hf
    modLog dimLog accLog eta hmodLog heta hacc hQlog hdim hlength
  have hmass := affine_parameter_bad_pair_probability parLo parHi hpar D Q B R r anchor hBQ hB hparamDim
    hparMin hparSide hparWidth
  have hgood (tu : (∀ j, Finset.Ico (parLo j) (parHi j)) × (∀ j, Finset.Ico (parLo j) (parHi j)))
      (htu : ¬ affineParameterBadPair D Q r anchor (fun j => (tu.1 j).val) (fun j => (tu.2 j).val)) :=
    retained_physical_residual_correlation_s2 k0 D r anchor parLo parHi tu.1 tu.2 H Q hH hL hC hκ hδ hδ1
      hleft hright hgap htu hmesh hsmall origin hZ lo N hside degree f f hf hf eta ρ modLog dimLog accLog
      hρ heta hmodLog hacc hQlog hdim hlarge hwhole hlength hQdegree
  have h := smooth_window_weighted_sampled_error (fun z => (origin z : ℝ))
    (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
    (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ hscale W hW
    (integerBoxUniformWeights parLo parHi hpar) (fun t j => anchor j + (D : ℤ) * (t j).val)
    (translatedIntegerBox lo N) e (physicalBoxResidual_zero_off lo N P hpos (boundedPrimePower Q) degree f)
    (by positivity : 0 ≤ 1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) hepsilon henergy
    (fun tu => affineParameterBadPair D Q r anchor (fun j => (tu.1 j).val) (fun j => (tu.2 j).val)) hmass hgood v hv
  simpa only [integerBoxUniformWeights_mean, smoothPairCoefficientScale] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem allocated_weighted_physical_replacement_s2_oai {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C κ A epsilon : ℝ} (Q : ℕ)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog : ℝ) (hmodLog : 0 ≤ modLog)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog) (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hsize : ∀ i, physicalReplacementScaleThreshold (Fintype.card I) k0 Q C κ A epsilon degree modLog dimLog *
      L ^ exponent ≤ H i)
    (hQdegree : Q ≤ 2 ^ degree)
    (B R : ℕ) (hBQ : D * B ≤ Q) (hB : 0 < B) (hparamDim : 2 ≤ Fintype.card J)
    (parMin : ℝ) (hparMin : 0 < parMin)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (W : Finset (Option J × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2)
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A epsilon
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA heps hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option J × I) *
        (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card) *
      Real.sqrt ((2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I *
        integerBoxBadPairBudget (Fintype.card J) B R r parMin + epsilon) := by
  let delta := physicalPairPointAccuracy (Fintype.card I) k0 Q C κ A epsilon
  let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A epsilon
  let eta := physicalPairMeanAccuracy (Fintype.card I) k0 Q C κ A degree epsilon
  let accLog := physicalMeanAccuracyLog (Fintype.card I) k0 Q C κ A degree epsilon
  have sc (i : I) := physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
    (zero_le_one.trans hC) hA heps hL hexponent (hsize i) (hupper i)
  have hH (i : I) : 0 < H i := (sc i).1
  have hlarge (i : I) : 4 ≤ rho * H i := (sc i).2.2.1
  have hwhole (i : I) : rho * H i ≤ 2 * N i := (sc i).2.2.2.2.2.2
  let P := normalizedBoxPartitions N H rho hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
  have hd := physicalPairPointAccuracy_spec (Fintype.card I) k0 Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec (Fintype.card I) k0 C κ hA heps
  have he := physicalPairMeanAccuracy_spec (Fintype.card I) k0 Q C κ degree hA heps
  have halog := physicalMeanAccuracyLog_spec (Fintype.card I) k0 Q C κ degree hA heps
  have hscale := smoothPairCoefficientScale_large (J := J) H hL
    (show 0 ≤ 8 * (probabilityProfileLipschitz : ℝ) by positivity) (fun i => (sc i).2.2.2.2.2.1)
  have hZ := shiftedSmoothProductMass_pos_of_large_scales (fun z => (origin z : ℝ))
    (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1) hscale
  have h := weighted_physical_replacement k0 D r anchor parLo parHi hpar H Q hH hL hC hκ hd.1.le hd.2.1
    hleft hright hgap (fun i => (sc i).2.1) hd.2.2.2 origin hZ lo N (fun i => (sc i).2.2.2.2.1)
    degree f hf eta rho modLog dimLog accLog hr.1.le he.2.1 hmodLog halog.2.le hQlog hdim hlarge hwhole
    (fun i => (sc i).2.2.2.1) hQdegree B R hBQ hB hparamDim parMin hparMin hparSide hparWidth hscale W hW v hv
  have hp := physicalResidualPairBudget_of_accuracies lo N H hH k0 Q C κ degree hA heps hratio
  have heta : 0 ≤ eta := he.1.le
  have hcap0 := residueTruncationCap_nonneg (BoundedPrime Q) degree heta
  have hcap := residueTruncationCap_le_envelope (BoundedPrime Q) degree he.2.1
  have hE : 1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2 ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0 hcap 2) heta
    have henergy := he.2.2.1
    change eta * residualCapEnvelope (BoundedPrime Q) degree ^ 2 ≤ 1 at henergy
    linarith
  have hvol := translated_box_volume_ratio_le lo N H hH hratio
  have henergy : (∏ i, 2 / H i) * ((1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) *
      (translatedIntegerBox lo N).card) ≤ (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I := by
    calc
      _ = ((2 : ℝ) ^ Fintype.card I * ((translatedIntegerBox lo N).card / ∏ i, H i)) *
          (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
        ring
      _ ≤ ((2 : ℝ) ^ Fintype.card I * A ^ Fintype.card I) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hvol (by positivity)) hE (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hbad : 0 ≤ integerBoxBadPairBudget (Fintype.card J) B R r parMin := by
    unfold integerBoxBadPairBudget
    positivity
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option J × I) *
      (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg (fun z _ => (smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1).le)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hfactor
  apply Real.sqrt_le_sqrt
  exact add_le_add (mul_le_mul_of_nonneg_right henergy hbad) hp

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.allocated_weighted_physical_replacement_s2_oai.{u_1, u_2} := @OAI.Erdos3.allocated_weighted_physical_replacement_s2_oai.{u_1, u_2}
