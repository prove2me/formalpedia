-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:38:05.887102+00:00
-- url     : https://prove2.me/submissions/7c1d3bce-15b6-4857-80b6-50f58fcf85f0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B245
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedForecastPolynomial_crt_decay_of_bad_product_s2
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_nonneg {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : 0 ≤ rationalOutputDensity p Y N b := by
  unfold rationalOutputDensity finiteImageMass
  exact mul_nonneg (Nat.cast_nonneg _) (p.mean_nonneg (fun _ => by split_ifs <;> norm_num))

theorem rationalInactiveForecast_nonneg {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : 0 ≤ gridVolume) (z : Z) (b : J → ZMod N) :
    0 ≤ rationalInactiveForecast inactive active gridPoint Y N gridVolume z b :=
  mul_nonneg hV (inactive.fiberMean_nonneg gridPoint z _
    (fun i => rationalOutputDensity_nonneg (active i) (Y i) N b))

end Erdos3

end

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

theorem rationalInactiveForecast_cap {I A Z : Type*} [Fintype I] [Fintype A]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (z : Z) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (1 + C) := by
  have hcap (i) := (rationalOutputDensity_order_bounds (active i) (Y i) N hC hP
    (hdecay i) 1 zero_lt_one).1 b
  unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  unfold FiniteProbabilityWeights.mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gridPoint i = z
  · simp only [hi, ite_true, mul_one]
    exact mul_le_mul_of_nonneg_left (hcap i) (inactive.nonneg i)
  · simp only [hi, ite_false, mul_zero, zero_mul, le_refl]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem modularForecastRankConstant_dimension (s D d : ℕ) (hd : d ≤ D) :
    ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) := by
  rw [modularForecastRankConstant_decay]
  exact_mod_cast Nat.add_le_add_right hd 2

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

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped Classical NNReal

theorem FiniteProbabilityWeights.toPMF_injective {X : Type*} [Fintype X] :
    Function.Injective (fun p : FiniteProbabilityWeights X => p.toPMF) := by
  intro p q hpq
  change p.toPMF = q.toPMF at hpq
  have hw : p.weight = q.weight := by
    funext x
    exact (FiniteProbabilityWeights.toPMF_toReal p x).symm.trans
      ((congrArg (fun μ : PMF X => (μ x).toReal) hpq).trans
        (FiniteProbabilityWeights.toPMF_toReal q x))
  cases p
  cases q
  cases hw
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedComplexChartSupport
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

theorem restrictedComplexChartDensity_norm_le (q : X → Y) (S : Set X)
    (hinj : Set.InjOn q S) (f : X → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖restrictedComplexChartDensity q S 1 f y‖ ≤ C := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S 1 f hinj hx, Complex.ofReal_one, one_mul]
    exact hf x
  · rw [restrictedComplexChartDensity_zero q S 1 f hy, norm_zero]
    exact hC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

theorem principalAffineIntervalLaw_mean (f : PrincipalIntegerTuples B h Empty L → ℝ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem zeroScalar_fin_mean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℝ) :
    (integerScalarCubeWeights Empty L hL).mean f = 𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  rw [integerScalarCubeWeights_mean]
  apply Fintype.expect_equiv
    ((zeroScalarCubeIntervalEquiv Empty L).trans (finIntegerIntervalEquiv L).symm)
  intro x
  congr 1
  funext a
  apply Subtype.ext
  cases a with
  | none =>
    have hx := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hx
    exact (Int.toNat_of_nonneg hx.1).symm
  | some a => exact isEmptyElim a

theorem zeroScalar_fin_complexMean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℂ) :
    (integerScalarCubeWeights Empty L hL).complexMean f =
      𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [← FiniteProbabilityWeights.uniform_complexMean]
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).im)

theorem integerScalarCubeWeights_pi_fin_complexMean
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : X → ℕ) (hH : ∀ i, 0 < H i)
    (f : (∀ i, IntegerScalarCubeBox Empty (H i)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights Empty (H i) (hH i))).complexMean f =
      𝔼 t : (∀ i, Fin (H i)), f (fun i => zeroScalarFinPoint (H i) (t i)) := by
  let : ∀ i, Nonempty (Fin (H i)) := fun i => ⟨⟨0, hH i⟩⟩
  have htransport := FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun i => integerScalarCubeWeights Empty (H i) (hH i))
    (fun i => FiniteProbabilityWeights.uniform (Fin (H i)))
    (fun _ x => x) (fun i => zeroScalarFinPoint (H i))
    (fun i g => (zeroScalar_fin_complexMean (H i) (hH i) g).trans
      (FiniteProbabilityWeights.uniform_complexMean _).symm) f
  exact htransport.trans (FiniteProbabilityWeights.pi_uniform_complexMean _)

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

theorem principalTupleWeights_fin_complexMean (f : PrincipalIntegerTuples B h Empty H → ℂ) :
    (principalTupleWeights (α := Empty) B h H hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  exact integerScalarCubeWeights_pi_fin_complexMean H hH f

theorem principalTupleWeights_fin_mean (f : PrincipalIntegerTuples B h Empty H → ℝ) :
    (principalTupleWeights (α := Empty) B h H hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  have he := congrArg Complex.re (principalTupleWeights_fin_complexMean B h H hH (fun z => (f z : ℂ)))
  rw [← FiniteProbabilityWeights.uniform_complexMean] at he
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re,
    FiniteProbabilityWeights.uniform_mean] using he

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem containedProgressionTupleMap_finPoint [Fintype D] [DecidableEq D]
    [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)]
    (t : ∀ j, Fin (H j)) :
    containedProgressionTupleMap B h L H step start hL hsubset (principalFinTuplePoint B h H t) =
      principalAffineIntervalPoint B h L H step start hinside t := by
  funext j a
  apply Subtype.ext
  have hc : IntegerScalarCube (H j) (fun a => (principalFinTuplePoint B h H t j a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero,
      principalFinTuplePoint, zeroScalarFinPoint]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩
  rw [containedProgressionTupleMap,
    containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ hc]
  cases a with
  | none => rfl
  | some a => exact isEmptyElim a

theorem principalAffineIntervalLaw_eq_contained :
    principalAffineIntervalLaw B h L H step start hinside hH =
      (principalTupleWeights (α := Empty) B h H hH).fiberLaw
        (containedProgressionTupleMap B h L H step start hL hsubset) := by
  have he (f : PrincipalIntegerTuples B h Empty L → ℝ) :
      (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
        ((principalTupleWeights (α := Empty) B h H hH).fiberLaw
          (containedProgressionTupleMap B h L H step start hL hsubset)).mean f := by
    rw [principalAffineIntervalLaw_mean, FiniteProbabilityWeights.fiberLaw_mean,
      principalTupleWeights_fin_mean]
    apply Finset.expect_congr rfl
    intro t _
    rw [containedProgressionTupleMap_finPoint B h H L step start hL hinside hsubset]
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  simpa [FiniteProbabilityWeights.mean] using he (fun y => if y = z then 1 else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

omit [∀ j, Fintype (I j)] in

theorem allocatedCongruenceForecastRankConstant_dimension
    (hm : 0 < m) (D : ℕ)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D) :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) := by
  apply modularForecastRankConstant_dimension
  rw [Fintype.card_sigma]
  exact (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans hD

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem principalLaw_eq_contained :
    slice.principalLaw =
      (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
        slice.principalLength slice.principalLength_pos).fiberLaw
      (containedProgressionTupleMap B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) slice.principalLength slice.principalStep
        slice.principalStart (allocatedPrincipalSides_pos B U b S) slice.principalSupport) := by
  exact principalAffineIntervalLaw_eq_contained B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos (allocatedPrincipalSides B U b S)
    slice.principalStep slice.principalStart (allocatedPrincipalSides_pos B U b S)
    slice.principalInside slice.principalSupport

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedInactiveGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalTarget_norm_le
    {M : ℝ} (hM : 0 ≤ M)
    (hsource : ∀ (z : A → ℤ) (outPoint : Out → ZMod N)
        (y : (Spatial → ℝ) × (Active → ℝ)),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N volume (fun a _ => z a) outPoint : ℂ)‖ ≤ M)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    ‖target poly hpoly u‖ ≤ M := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hbound (z : MixedCoveredJetSource I single Eout n N) :
      ‖chartSource u z‖ ≤ M := by
    exact hsource _ _ _
  have h := restrictedComplexChartDensity_norm_le chart region hinj (chartSource u)
    hM hbound (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))
  simpa only [forecastLawDensityPhysicalTarget] using h

theorem forecastLawDensityPhysicalTarget_norm_le_of_decay
    {H Icap C P : ℝ} (hH : 0 ≤ H) (hIcap : 0 ≤ Icap)
    (hV : 0 ≤ volume) (hC : 0 ≤ C)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun t j => (Y i t j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    ‖target poly hpoly u‖ ≤ H * Icap * (1 + C) := by
  apply forecastLawDensityPhysicalTarget_norm_le B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW
    (M := H * Icap * (1 + C)) (by positivity) _ poly hpoly u
  intro z outPoint y
  let F := forecastInactiveFixedOutput B U basis S selected
    (allocatedOriginalSampleInactiveCoefficients B selected sample) x
  have hcap := rationalInactiveForecast_cap law active F Y N hV hC hP hdecay
    (fun a _ => z a) outPoint
  have hnonneg := rationalInactiveForecast_nonneg law active F Y N hV
    (fun a _ => z a) outPoint
  have hrat : rationalInactiveForecast law active F Y N volume (fun a _ => z a) outPoint ≤
      Icap * (1 + C) := hcap.trans
    (mul_le_mul_of_nonneg_right (hgrid z) (add_nonneg zero_le_one hC))
  change ‖(density y : ℂ) *
    (rationalInactiveForecast law active F Y N volume (fun a _ => z a) outPoint : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  calc
    _ ≤ H * (Icap * (1 + C)) := mul_le_mul (hDensity y) hrat hnonneg hH
    _ = _ := (mul_assoc _ _ _).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

theorem target_norm_le_s2_oai
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
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
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
    (u : integerBox physicalN) :
    let cap := (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice : ℝ)
    let Cdecay := (((slice.path.Rbad * ∏ q : slice.path.primes,
      q.val ^ slice.path.prescribed q.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m))
    ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
      s.κ * cap * Ctail ^ Fintype.card A * (1 + Cdecay) := by
  intro cap Cdecay
  let := slice.path.primeNeZero
  let N := ∏ q : slice.path.primes, q.val ^ slice.path.exponent q.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩
  let inactive := allocatedShortAxis (I := I) U b S.value
  let poly := allocatedForecastPolynomial inactive slice.path.base slice.path.noise
    (allocatedReadDeck slice.path.read) (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun q : slice.path.primes => q.val)
    (fun q : slice.path.primes => slice.path.exponent q.val)
    (fun q : slice.path.primes => slice.path.prescribed q.val)
    (primePower_crt_coprime (fun q : slice.path.primes => q.val)
      (fun q : slice.path.primes => slice.path.exponent q.val)
      (fun q => slice.path.prime q.val q.property) Subtype.val_injective) slice.path.origin
  let Out := Sigma (AllocatedCongruenceRankOutput X Eout inactive)
  let coeff := allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hc := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U b hR hσ S slice.path.sample slice.path.hs
  have hmass (z : A → ℤ) :
      (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
        slice.principalLaw.fiberMean
          (forecastInactiveFixedOutput B U b S selected coeff slice.path.commonTuple)
          (fun a _ => z a) (fun _ => 1) ≤ Ctail ^ Fintype.card A := by
    rw [slice.principalLaw_eq_contained]
    exact forecastInactive_sliced_fixed_grid_mass_le_s2 B U b hR hσ S
      slice.principalLength slice.principalStep slice.principalStart slice.principalLength_pos
      slice.principalSupport selected s.hselected δ Ptail Hchild hδ hreg s.hsmall hgrid
      coeff hc s.L s.hL hPtail (s.hprimitiveCap.trans hsPtail) hstrideTail s.hB
      Ctail hCtail htailactual slice.path.commonTuple z
  have hCdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension inactive s.hm Dmod s.hDmod
  have hdecay (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product_s2 inactive slice.path.noise
      (allocatedReadDeck slice.path.read) (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
      spatial kernel block s.hm slice.path.primes slice.path.exponent slice.path.prescribed
      slice.path.prime (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _)
      slice.path.Rbad slice.path.hbad slice.path.base slice.path.origin
      (fun k => (v k.1 k.2 : ℤ)) χ
  have ht := forecastLawDensityPhysicalTarget_norm_le_of_decay B U b S slice.principalLaw
    (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (H := cap) (Icap := Ctail ^ Fintype.card A)
    (C := Cdecay) (NNReal.coe_nonneg _) (pow_nonneg hCtail _)
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hCdecay
    (slice.density_bounds_s2 s.hBactive s.hδslice).1 hmass hPdecay hdecay
    (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val
  change ‖(s.κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg s.hκ]
  calc
    _ ≤ s.κ * (cap * Ctail ^ Fintype.card A * (1 + Cdecay)) :=
      mul_le_mul_of_nonneg_left ht s.hκ
    _ = _ := by ring

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le_s2_oai
