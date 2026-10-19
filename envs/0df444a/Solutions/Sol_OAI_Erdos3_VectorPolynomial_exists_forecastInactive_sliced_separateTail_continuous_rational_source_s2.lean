-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:32:09.607037+00:00
-- url     : https://prove2.me/submissions/2a7355b8-230d-4791-a124-610e6fce05d2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B197
import Definitions.Def_OAIE3v2B301
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_retained_character_sites_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_grid_mass_le_s2

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

theorem torsionLatticeCharacter_card_le (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype.card (TorsionLatticeCharacter I a) ≤ a ^ Fintype.card I := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective torsionCharacterCoordinates
    (torsionCharacterCoordinates_injective (I := I) (a := a))
  have hc : Fintype.card (rootsOfUnity a ℂ) = a := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  rw [Fintype.card_fun, hc] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_series_truncation_le {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (c ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k‖ ≤ spectrumTail S (fun k => ‖c k‖) := by
  have hid : (∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k =
      ∑ k, if k ∈ S then 0 else c k * ψ k := by
    calc
      _ = ∑ k, (c k * ψ k - if k ∈ S then c k * ψ k else 0) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, sub_self, sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp only [hk, ite_true, norm_zero, le_refl]
  · simp only [hk, ite_false, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageCharacteristic_norm_le_one {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) :
    ‖finiteImageCharacteristic p Y χ‖ ≤ 1 := by
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [AddChar.norm_apply, p.mean_const])

theorem finiteImageFourier_inversion {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    (∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z)) =
      (Fintype.card H : ℂ) * finiteImageMass p Y z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) * (∑ χ : AddChar H ℂ, χ (Y x - z)) := by
      simp only [finiteImageCharacteristic, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = (Fintype.card H : ℂ) * finiteImageMass p Y z := by
      simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Y x = z <;> simp [hx, mul_comm]

theorem finiteImageFourier_truncation {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (S : Finset (AddChar H ℂ)) (z : H)
    {scale : ℝ} (hscale : 0 ≤ scale) :
    ‖(scale : ℂ) * finiteImageMass p Y z -
      ((scale : ℂ) / Fintype.card H) * ∑ χ ∈ S, finiteImageCharacteristic p Y χ * star (χ z)‖ ≤
      (scale / Fintype.card H) * spectrumTail S (fun χ => ‖finiteImageCharacteristic p Y χ‖) := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (scale : ℂ) * finiteImageMass p Y z = ((scale : ℂ) / Fintype.card H) *
      ∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z) := by
    rw [finiteImageFourier_inversion]
    field_simp
  rw [he, ← mul_sub, norm_mul]
  have hn : ‖(scale : ℂ) / Fintype.card H‖ = scale / Fintype.card H := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hscale, Complex.norm_natCast]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_series_truncation_le S _ (fun χ => star (χ z))
    (fun χ => by simp only [norm_star, AddChar.norm_apply, le_refl])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I H : Type*} [Fintype I]
  [AddCommGroup H] [Fintype H]

theorem finiteCharacter_exactOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (q : ℕ) (hq : 0 < q) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q)).card ≤ q ^ Fintype.card I := by
  let : NeZero q := ⟨hq.ne'⟩
  let f : {χ : AddChar H ℂ // orderOf χ = q} → TorsionLatticeCharacter I q :=
    fun χ => ⟨characterPullback π χ.val, by
      simpa only [map_pow, map_one, χ.property] using
        congrArg (characterPullback π) (pow_orderOf_eq_one χ.val)⟩
  have hf : Function.Injective f := by
    intro χ ψ h
    apply Subtype.ext
    exact AddChar.compAddMonoidHom_injective_left π hπ (congrArg Subtype.val h)
  have hc := (Fintype.card_le_of_injective f hf).trans (torsionLatticeCharacter_card_le I q)
  simpa only [Fintype.card_subtype] using hc

theorem finiteCharacter_boundedOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (T : ℕ) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)).card ≤
      T ^ (Fintype.card I + 1) := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf (Finset.Icc 1 T) := by
    intro χ hχ
    exact Finset.mem_Icc.mpr ⟨(isOfFinOrder_of_finite χ).orderOf_pos,
      (Finset.mem_filter.mp hχ).2⟩
  change S.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 T, T ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hc := finiteCharacter_exactOrder_card_le π hπ q hq0
      have hsub : S.filter (fun χ => orderOf χ = q) ⊆
          Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q) := by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩
      exact (Finset.card_le_card hsub).trans
        (hc.trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp hq).2 _))
    _ = T ^ (Fintype.card I + 1) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, pow_succ]
      simp only [Nat.add_sub_cancel]
      exact Nat.mul_comm _ _

theorem finiteImage_boundedOrder_coefficient_mass {X : Type*} [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) (T : ℕ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T),
      ‖finiteImageCharacteristic p Y χ‖) ≤ (T : ℝ) ^ (Fintype.card I + 1) := by
  calc
    _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T), (1 : ℝ) :=
      Finset.sum_le_sum (fun χ _ => finiteImageCharacteristic_norm_le_one p Y χ)
    _ = ((Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast finiteCharacter_boundedOrder_card_le π hπ T

theorem finiteCharacter_order_tail
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (f : AddChar H ℂ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, f χ ≤ C / (orderOf χ : ℝ) ^ (Fintype.card I + 2))
    (T : ℕ) (hT : 0 < T) :
    spectrumTail (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) f ≤ C / T := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => T < orderOf χ)
  let orders := S.image (fun χ => orderOf χ)
  have heq : spectrumTail (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) f =
      ∑ χ ∈ S, f χ := by
    simp only [spectrumTail, S, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : orderOf χ ≤ T <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_ge]
  rw [heq, ← Finset.sum_fiberwise_of_maps_to (fun χ hχ => Finset.mem_image_of_mem (fun ψ => orderOf ψ) hχ) f]
  change (∑ q ∈ orders, ∑ χ ∈ S with orderOf χ = q, f χ) ≤ _
  have horders (q) (hq : q ∈ orders) : T < q := by
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hχ).2
  have hinner (q) (hq : q ∈ orders) :
      (∑ χ ∈ S with orderOf χ = q, f χ) ≤ C / (q : ℝ) ^ 2 := by
    have hqpos : 0 < q := hT.trans (horders q hq)
    have hqreal : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
    have hc : (S.filter (fun χ => orderOf χ = q)).card ≤ q ^ Fintype.card I :=
      (Finset.card_le_card (by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩)).trans
          (finiteCharacter_exactOrder_card_le π hπ q hqpos)
    calc
      _ ≤ ∑ _χ ∈ S with orderOf _χ = q, C / (q : ℝ) ^ (Fintype.card I + 2) := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa only [(Finset.mem_filter.mp hχ).2] using hdecay χ
      _ = (S.filter (fun χ => orderOf χ = q)).card *
          (C / (q : ℝ) ^ (Fintype.card I + 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ) ^ Fintype.card I * (C / (q : ℝ) ^ (Fintype.card I + 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = C / (q : ℝ) ^ 2 := by rw [pow_add]; field_simp
  calc
    _ ≤ ∑ q ∈ orders, C / (q : ℝ) ^ 2 := Finset.sum_le_sum hinner
    _ = C * ∑ q ∈ orders, 1 / (q : ℝ) ^ 2 := by simp only [Finset.mul_sum, mul_one_div]
    _ ≤ C * (1 / (T : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail orders hT horders) hC
    _ = C / T := mul_one_div _ _

theorem finiteImage_density_order_truncation {X : Type*} [Fintype X] [DecidableEq H]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, ‖finiteImageCharacteristic p Y χ‖ ≤
      C / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (T : ℕ) (hT : 0 < T) (z : H) :
    ‖(Fintype.card H : ℂ) * finiteImageMass p Y z -
      ∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T),
        finiteImageCharacteristic p Y χ * star (χ z)‖ ≤ C / T := by
  have he := finiteImageFourier_truncation p Y
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) z (Nat.cast_nonneg (Fintype.card H))
  have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Complex.ofReal_natCast, div_self hcard, div_self hcardC, one_mul] at he
  exact he.trans (finiteCharacter_order_tail π hπ _ hC hdecay T hT)

theorem finiteImage_density_bound_of_order_decay {X : Type*} [Fintype X] [DecidableEq H]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, ‖finiteImageCharacteristic p Y χ‖ ≤
      C / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (z : H) :
    (Fintype.card H : ℝ) * finiteImageMass p Y z ≤ 1 + C := by
  have hset : Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ 1) = {1} := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact orderOf_eq_one_iff.mp (Nat.le_antisymm h (isOfFinOrder_of_finite χ).orderOf_pos)
    · intro h
      subst χ
      simp
  have he := finiteImage_density_order_truncation π hπ p Y hC hdecay 1 zero_lt_one z
  rw [hset] at he
  simp only [Finset.sum_singleton, finiteImageCharacteristic, AddChar.one_apply,
    FiniteProbabilityWeights.complexMean_const, star_one, mul_one, Nat.cast_one, div_one] at he
  have hre : |(Fintype.card H : ℝ) * finiteImageMass p Y z - 1| ≤ C := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using he
  linarith [(abs_le.mp hre).2]

theorem finiteCharacter_integer_decay_of_rpow {C P : ℝ} (hC : 0 ≤ C)
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P) (f : AddChar H ℂ → ℝ)
    (hf : ∀ χ, f χ ≤ C * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ, f χ ≤ C / (orderOf χ : ℝ) ^ (Fintype.card I + 2) := by
  intro χ
  have hq : (1 : ℝ) ≤ orderOf χ := by
    exact_mod_cast (isOfFinOrder_of_finite χ).orderOf_pos
  have hq0 : 0 < (orderOf χ : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hpow : (orderOf χ : ℝ) ^ (Fintype.card I + 2) ≤ (orderOf χ : ℝ) ^ P := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hP
  apply (hf χ).trans
  rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC (pow_pos hq0 _) hpow

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem integerResidueTuple_surjective (N : ℕ) :
    Function.Surjective (integerResidueTuple (J := J) N) := by
  intro y
  choose x hx using fun j => ZMod.intCast_surjective (y j)
  exact ⟨x, funext hx⟩

theorem rationalOutputDensity_order_bounds
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (J → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    (∀ b, rationalOutputDensity p Y N b ≤ 1 + C) ∧
    S.card ≤ T ^ (Fintype.card J + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖) ≤
      (T : ℝ) ^ (Fintype.card J + 1) ∧
    ∀ b, ‖(rationalOutputDensity p Y N b : ℂ) -
      ∑ χ ∈ S, finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)‖
        ≤ C / T := by
  have hd := finiteCharacter_integer_decay_of_rpow (I := J) hC hP _ hdecay
  let π := integerResidueTuple (J := J) N
  have hπ : Function.Surjective π := integerResidueTuple_surjective N
  refine ⟨fun b => finiteImage_density_bound_of_order_decay π hπ p _ hC hd b,
    finiteCharacter_boundedOrder_card_le π hπ T,
    finiteImage_boundedOrder_coefficient_mass π hπ p _ T, ?_⟩
  intro b
  simpa only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast] using
    finiteImage_density_order_truncation π hπ p _ hC hd T hT b

theorem rationalInactiveForecast_order_truncation {I A Z : Type*} [Fintype I] [Fintype A]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) -
      (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active i)
          (fun x j => (Y i x j : ZMod N)) χ * star (χ b) else 0)‖ ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) := by
  let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
  let trunc (i : I) : ℂ := ∑ χ ∈ S, finiteImageCharacteristic (active i)
    (fun x j => (Y i x j : ZMod N)) χ * star (χ b)
  have heq : (rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) =
      (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
        (rationalOutputDensity (active i) (Y i) N b : ℂ) else 0) := by
    unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
    rw [Complex.ofReal_mul, ← inactive.complexMean_ofReal]
    congr 2
    funext i
    split_ifs <;> rfl
  change ‖_ - (gridVolume : ℂ) * inactive.complexMean
    (fun i => if gridPoint i = z then trunc i else 0)‖ ≤ _
  rw [heq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hV, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  calc
    _ ≤ inactive.mean (fun i => if gridPoint i = z then C / T else 0) := by
      apply inactive.norm_complexMean_sub_le
      intro i _
      by_cases hi : gridPoint i = z
      · simp only [hi, ite_true]
        exact (rationalOutputDensity_order_bounds (active i) (Y i) N hC hP
          (hdecay i) T hT).2.2.2 b
      · simp only [hi, ite_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold FiniteProbabilityWeights.fiberMean FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : gridPoint i = z <;> simp [hi]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_order_truncation_separated
    {I A J Z : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J] [DecidableEq Z]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) -
      ∑ χ : S, (gridVolume : ℂ) * inactive.complexMean (fun i =>
        finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b)‖ ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) := by
  intro S
  have h := rationalInactiveForecast_order_truncation inactive active gridPoint Y N hV hC hP
    hdecay T hT z b
  dsimp only at h
  have hi (i : I) :
      (if gridPoint i = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ *
          star (χ b) else 0) =
      ∑ χ : S, (finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
        (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b) := by
    by_cases hz : gridPoint i = z
    · simp only [hz, ite_true, mul_one]
      exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    · simp only [hz, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]
  have hsep : (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
      ∑ χ ∈ S, finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ *
        star (χ b) else 0) =
      ∑ χ : S, (gridVolume : ℂ) * inactive.complexMean (fun i =>
        finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b) := by
    simp_rw [hi]
    unfold FiniteProbabilityWeights.complexMean
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hsep]
  convert h using 1
  congr 4
  funext i
  split_ifs <;> rfl

theorem rationalInactiveForecast_retained_approximation
    {I A J Z : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J] [DecidableEq Z]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P err : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) (model : ℂ)
    (hret :
      ‖(∑ χ : Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T),
        (gridVolume : ℂ) * inactive.complexMean (fun i =>
          finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b)) - model‖ ≤ err) :
      ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) - model‖ ≤
        gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) + err := by
  have htail := rationalInactiveForecast_order_truncation_separated inactive active gridPoint Y N
    hV hC hP hdecay T hT z b
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add htail hret)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_axis_product_lipschitz (f : A → ℝ → ℂ) (L : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hn : ∀ a x, ‖f a x‖ ≤ 1) :
    (∀ x : A → ℝ, ‖∏ a, f a (x a)‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (fun x : A → ℝ => ∏ a, f a (x a)) := by
  have hl (a : A) : LipschitzWith L (fun x : A → ℝ => f a (x a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a) L.coe_nonneg)
  simpa only [NNReal.coe_one, one_pow, mul_one] using
    bounded_lipschitz_fintype_prod (fun a (x : A → ℝ) => f a (x a))
      (B := 1) le_rfl hl (fun a x => hn a (x a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

include h in
omit [Fintype S] in
theorem siteFamilyFactor_bounds (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖siteFamilyFactor e k s r x‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (siteFamilyFactor e k s r) := by
  exact finite_site_axis_product_lipschitz (fun a => (e a).factor (k a) s (r a)) L
    (fun a => (h a).lipschitz (k a) s (r a)) (fun a => (h a).factor_bound (k a) s (r a))

include h in
omit [Fintype S] in
theorem siteFamilyFactor_support (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : A → ℝ)
    (hx : ∃ a, H a ≤ |x a|) : siteFamilyFactor e k s r x = 0 := by
  obtain ⟨a, ha⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ a) ((h a).support (k a) s (r a) (x a) ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastContinuousNormalization
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem forecastContinuous_normalized_bounds {Y : Type*} [PseudoMetricSpace Y]
    (density : Y → ℝ) (H : ℝ) (hH : 1 ≤ H) (hcap : ∀ y, ‖density y‖ ≤ H)
    (LG : ℝ≥0) (hLG : LipschitzWith LG density) :
    (∀ y, ‖(density y : ℂ) / (H : ℂ)‖ ≤ 1) ∧
      LipschitzWith LG (fun y => (density y : ℂ) / (H : ℂ)) ∧
      ∀ y, (density y : ℂ) = (H : ℂ) * ((density y : ℂ) / (H : ℂ)) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast hHpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hHpos.le]
    exact (div_le_one hHpos).mpr (hcap y)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← sub_div, ← Complex.ofReal_sub, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hHpos.le]
    exact (div_le_self (norm_nonneg _) hH).trans
      (by simpa only [dist_eq_norm] using hLG.dist_le_mul x y)
  · intro y
    exact (mul_div_cancel₀ (density y : ℂ) hHne).symm

theorem forecastContinuous_scaled_error {Y : Type*}
    (density : Y → ℝ) (H : ℝ) (hH : 1 ≤ H) (hcap : ∀ y, ‖density y‖ ≤ H)
    (y : Y) {target model : ℂ} {ε : ℝ} (happrox : ‖target - model‖ ≤ ε) :
    ‖(density y : ℂ) * target - (density y : ℂ) * model‖ ≤ H * ε := by
  rw [← mul_sub, norm_mul, Complex.norm_real]
  exact mul_le_mul (hcap y) happrox (norm_nonneg _) (zero_le_one.trans hH)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}
variable [Fintype R] [Fintype A] [Fintype S]
variable (e : R → A → ScalarSiteExpansion.{v,w} S)

omit [Fintype R] [Fintype S] in

theorem forecastSiteMixture_factor_comp_bounds
    {X : Type*} [PseudoMetricSpace X]
    {T D C H : A → ℝ} {L K Kcoord : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : X → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1) (hGL : LipschitzWith K G)
    (coord : X → A → ℝ) (hcoord : LipschitzWith Kcoord coord)
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    (∀ x, ‖(χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x)‖ ≤ 1) ∧
      LipschitzWith (K + (Fintype.card A * L) * Kcoord)
        (fun x => (χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x)) := by
  obtain ⟨hb, hL⟩ := siteFamilyFactor_bounds (e t.1) (he t.1) t.2 s r
  have hχG : ∀ x, ‖χ * G x‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    exact (mul_le_mul hχ (hG x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hχGL : LipschitzWith K (fun x => χ * G x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hχ).trans
      (by simpa only [dist_eq_norm] using hGL.dist_le_mul x y)
  refine ⟨fun x => ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul (hχG x) (hb (coord x)) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simpa only [one_mul, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds (fun x => χ * G x)
        (fun x => siteFamilyFactor (e t.1) t.2 s r (coord x))
        hχGL (hL.comp hcoord) (Bf := 1) (Bg := 1) hχG (fun x => hb (coord x))

omit [Fintype R] [Fintype S] in
theorem forecastSiteMixture_factor_comp_support
    {X : Type*} {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : X → ℂ) (coord : X → A → ℝ) (χ : ℂ) (x : X)
    (hx : ∃ a, H a ≤ |coord x a|) :
    (χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x) = 0 := by
  rw [siteFamilyFactor_support (e t.1) (he t.1) t.2 s r (coord x) hx, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

private theorem forecast_singleton_site_eval
    {A : Type*} [Fintype A] (e : A → ScalarSiteExpansion (Finset Empty))
    (z : A → ℤ) (x : A → ℝ) :
    siteFamilyEval e (fun _ => z) (fun _ => x) =
      ∑ k, siteFamilyCoefficient e k * siteFamilyFactor e k ∅
        (fun a => (z a : ZMod ((e a).period (k a)))) x := by
  simp only [siteFamilyEval, Fintype.prod_unique]
  rfl

theorem forecastRetained_normalized_expansion
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    (c : ∀ q, Cell q → ℂ) (phase : Q → ℂ)
    (z : A → ℤ) (x : A → ℝ) (G H F : ℂ) (hG : G = H * F) :
    G * (∑ q, (∑ r, c q r * siteFamilyEval (e q r) (fun _ => z) (fun _ => x)) * phase q) =
      ∑ t : Σ q, Σ r : Cell q, ∀ a, (e q r a).Term,
        (H * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2) *
          ((phase t.1 * F) * siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) x) := by
  simp_rw [forecast_singleton_site_eval]
  rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum, Finset.sum_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [forecastSiteMixtureCoefficient]
  rw [hG]
  ring

theorem forecastRetained_normalized_coefficient_mass
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    (c : ∀ q, Cell q → ℂ) {H M : ℝ} (hH : 0 ≤ H)
    (hmass : (∑ q, ∑ t : Σ r : Cell q, ∀ a, (e q r a).Term,
      ‖forecastSiteMixtureCoefficient (e q) (c q) t‖) ≤ M) :
    (∑ t : Σ q, Σ r : Cell q, ∀ a, (e q r a).Term,
      ‖(H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2‖) ≤ H * M := by
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hH, Fintype.sum_sigma]
  simp only [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (by simpa only [Fintype.sum_sigma] using hmass) hH

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {ContinuousCoord : Type*} [PseudoMetricSpace ContinuousCoord]
variable (density : ContinuousCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
variable (hdensity : ∀ y, ‖density y‖ ≤ H)
variable (densityLip : ℝ≥0) (hLip : LipschitzWith densityLip density)

include hH hdensity hLip in

theorem forecastContinuous_site_factor_bounds
    {A Cell Site : Type*} [Fintype A]
    (e : Cell → A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ cell a, (e cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (t : Σ cell, ∀ a, (e cell a).Term) (site : Site)
    (res : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    let F := fun y : ContinuousCoord × (A → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let factor := fun y : ContinuousCoord × (A → ℝ) =>
      (χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2
    (∀ y, ‖factor y‖ ≤ 1) ∧
      LipschitzWith (densityLip + Fintype.card A * Lsite) factor ∧
      (∀ y, (∃ a, Hsite a ≤ |y.2 a|) → factor y = 0) ∧
      (∀ y, (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
        (H : ℂ) * factor y) := by
  intro F factor
  have hb := forecastContinuous_normalized_bounds density H hH hdensity densityLip hLip
  have hF : ∀ y : ContinuousCoord × (A → ℝ), ‖F y‖ ≤ 1 := fun y => hb.1 y.1
  have hFL : LipschitzWith densityLip F := by
    simpa only [Function.comp_def, mul_one] using hb.2.1.comp
      (LipschitzWith.prod_fst (α := ContinuousCoord) (β := A → ℝ))
  have hf := forecastSiteMixture_factor_comp_bounds e he t site res F hF hFL Prod.snd
    (LipschitzWith.prod_snd (α := ContinuousCoord) (β := A → ℝ)) χ hχ
  refine ⟨hf.1, ?_, ?_, ?_⟩
  · simpa only [mul_one] using hf.2
  · intro y hy
    exact forecastSiteMixture_factor_comp_support e he t site res F Prod.snd χ y hy
  · intro y
    have hn : (density y.1 : ℂ) = (H : ℂ) * F y := hb.2.2 y.1
    change (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
      (H : ℂ) * ((χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2)
    rw [hn]
    ring

include hH hdensity hLip in

theorem forecastRetained_continuous_expansion
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ q cell a, (e q cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (c : ∀ q, Cell q → ℂ) (phase : Q → ℂ) (hphase : ∀ q, ‖phase q‖ ≤ 1)
    {M : ℝ} (hmass : (∑ q, ∑ t : Σ cell : Cell q, ∀ a, (e q cell a).Term,
      ‖forecastSiteMixtureCoefficient (e q) (c q) t‖) ≤ M) :
    let F := fun y : ContinuousCoord × (A → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let Term := Σ q, Σ cell : Cell q, ∀ a, (e q cell a).Term
    let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2
    let factor := fun (t : Term) (z : A → ℤ) (y : ContinuousCoord × (A → ℝ)) =>
      (phase t.1 * F y) * siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
        (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
    (∑ t : Term, ‖coeff t‖) ≤ H * M ∧
      (∀ t z y, ‖factor t z y‖ ≤ 1) ∧
      (∀ t z, LipschitzWith (densityLip + Fintype.card A * Lsite) (factor t z)) ∧
      ∀ (z : A → ℤ) (y : ContinuousCoord × (A → ℝ)),
        (density y.1 : ℂ) *
          (∑ q, (∑ cell, c q cell * siteFamilyEval (e q cell)
            (fun _ => z) (fun _ => y.2)) * phase q) =
          ∑ t : Term, coeff t * factor t z y := by
  intro F Term coeff factor
  have hb := forecastContinuous_normalized_bounds density H hH hdensity densityLip hLip
  have hterm (t : Term) (z : A → ℤ) :=
    forecastContinuous_site_factor_bounds density H hH hdensity densityLip hLip
      (e t.1) (he t.1) t.2 ∅
      (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) (phase t.1) (hphase t.1)
  refine ⟨forecastRetained_normalized_coefficient_mass e c (zero_le_one.trans hH) hmass,
    (fun t z => (hterm t z).1), (fun t z => (hterm t z).2.1), ?_⟩
  intro z y
  exact forecastRetained_normalized_expansion e c phase z y.2
    (density y.1 : ℂ) (H : ℂ) (F y) (hb.2.2 y.1)

omit [PseudoMetricSpace ContinuousCoord] in
include hH hdensity in

theorem forecastRetained_continuous_error (y : ContinuousCoord)
    {target model : ℂ} {ε : ℝ} (happrox : ‖target - model‖ ≤ ε) :
    ‖(density y : ℂ) * target - (density y : ℂ) * model‖ ≤ H * ε :=
  forecastContinuous_scaled_error density H hH hdensity y happrox

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_2
theorem exists_forecastInactive_sliced_rational_site_approximation
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay)) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ) (weight χ) t‖) ≤
        (T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          (∑ χ : Ch, (∑ r : Pos χ, weight χ r *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) *
              star (χ.val outPoint))‖ ≤
          (∏ a, (height a : ℝ)) * law.fiberMean
            (forecastInactiveFixedOutput B U basis S selected coefficients x)
            (fun a _ => z a) (fun _ => 1) * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout := by
  intro p map law Ch Pos height weight
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_sliced_retained_character_sites_s2
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
  refine ⟨e, he, hmass, ?_⟩
  intro x z outPoint
  apply rationalInactiveForecast_retained_approximation law (fun _ => pRat)
    (forecastInactiveFixedOutput B U basis S selected coefficients x)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (show 0 ≤ ∏ a, (height a : ℝ) from
      Finset.prod_nonneg (fun a _ => Nat.cast_nonneg (height a))) hCdecay hPdecay hdecay
    T hT (fun a _ => z a) outPoint _
  simpa only [Complex.ofReal_prod, Complex.ofReal_natCast] using herr x z outPoint

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_3
theorem exists_forecastInactive_sliced_continuous_rational_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * ((∏ a, (height a : ℝ)) * law.fiberMean
            (forecastInactiveFixedOutput B U basis S selected coefficients x)
            (fun a _ => z a) (fun _ => 1) * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun _ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_sliced_rational_site_approximation
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
    hCdecay hPdecay hdecay
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  have hext (outPoint : Out → ZMod N) := forecastRetained_continuous_expansion
    density Hdensity hHdensity hdensity densityLip hdensityLip e he weight
    (fun χ : Ch => star (χ.val outPoint))
    (fun _ => by simp only [norm_star, AddChar.norm_apply]; exact le_rfl) hmass
  refine ⟨(hext 0).1, (fun b t z => (hext b).2.1 t z),
    (fun b t z => (hext b).2.2.1 t z), ?_⟩
  intro x z outPoint y
  have hfinal := forecastRetained_continuous_error density Hdensity hHdensity hdensity y (herr x z outPoint)
  rw [(hext outPoint).2.2.2 z (y, fun a => (z a : ℝ) / height a)] at hfinal
  exact hfinal

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_9
theorem exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2_oai
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hrest⟩ := exists_forecastInactive_sliced_continuous_rational_source
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
    hCdecay hPdecay hdecay density Hdensity hHdensity hdensity densityLip hdensityLip
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, ?_⟩
  intro x z outPoint y
  have hcap := forecastInactive_sliced_fixed_grid_mass_le_s2
    B U basis hR hσ S H step c hH hsubset selected hselected δ Ptail Hchild hδ hreg hsmall hgrid
    coefficients hcoefficients L hL hPtail hsPtail hstrideTail hB Ctail hCtail
    htailactual x z
  exact (hrest.2.2.2 x z outPoint y).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hcap (div_nonneg hCdecay (Nat.cast_nonneg T))) le_rfl)
      (zero_le_one.trans hHdensity))

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
