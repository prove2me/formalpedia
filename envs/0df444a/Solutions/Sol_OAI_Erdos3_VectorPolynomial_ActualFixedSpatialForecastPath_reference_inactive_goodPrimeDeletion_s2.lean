-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:42:15.113983+00:00
-- url     : https://prove2.me/submissions/beb41065-5677-4347-bdc7-8c709514a318

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B246
import Definitions.Def_OAIE3v2B252
import Theorems.Thm_OAI_Erdos3_primePower_polynomial_image_characteristic_decay_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteImageProducts
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageMass_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Z : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Z d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → Z d) (z : ∀ d, Z d) :
    finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
  classical
  have h := FiniteProbabilityWeights.eventProbability_pi p (fun d x => Y d x = z d)
  have he : finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      (FiniteProbabilityWeights.pi p).eventProbability (fun x => ∀ d, Y d (x d) = z d) := by
    unfold finiteImageMass FiniteProbabilityWeights.eventProbability
    congr 1
    funext x
    by_cases hx : ∀ d, Y d (x d) = z d
    · simp [hx]
    · have hf : (fun d => Y d (x d)) ≠ z := fun e => hx (fun d => congrFun e d)
      simp only [hf, hx, ite_false]
  have hr : (∏ d, (p d).eventProbability (fun x => Y d x = z d)) =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
    apply Finset.prod_congr rfl
    intro d _
    unfold FiniteProbabilityWeights.eventProbability finiteImageMass
    congr 1
    funext x
    by_cases hx : Y d x = z d <;> simp only [hx, ite_true, ite_false]
  exact he.trans (h.trans hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_mul_prod_one_add_le_one {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) :
    (1 - ∑ i ∈ S, e i) * (∏ i ∈ S, (1 + e i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have heS : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg heS
    have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [heS i hi])
    have hstep : (1 - (e a + ∑ i ∈ S, e i)) * (1 + e a) ≤ 1 - ∑ i ∈ S, e i := by
      nlinarith [mul_nonneg hea hs, sq_nonneg (e a)]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep hp).trans (ih heS)

theorem prod_one_add_le_one_add_twice_sum {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    (∏ i ∈ S, (1 + e i)) ≤ 1 + 2 * ∑ i ∈ S, e i := by
  have h := one_sub_sum_mul_prod_one_add_le_one S e he
  have hs := Finset.sum_nonneg he
  have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [he i hi])
  have hp2 : (∏ i ∈ S, (1 + e i)) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 hs]

theorem positive_prod_sub_one_le_twice_sum {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herror : ∀ i ∈ S, |f i - 1| ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    |(∏ i ∈ S, f i) - 1| ≤ 2 * ∑ i ∈ S, e i := by
  have hs := Finset.sum_nonneg he
  have he1 (i) (hi : i ∈ S) : e i ≤ 1 :=
    (Finset.single_le_sum he hi).trans (hsmall.trans (by norm_num))
  have hlo := one_sub_sum_le_positive_prod S f e hf (fun i hi => ⟨he i hi, he1 i hi⟩)
    (fun i hi => by have h := (abs_le.mp (herror i hi)).1; linarith)
  have hhi : (∏ i ∈ S, f i) ≤ 1 + 2 * ∑ i ∈ S, e i := by
    apply (Finset.prod_le_prod hf (fun index hindex => ?_)).trans
      (prod_one_add_le_one_add_twice_sum S e he hsmall)
    have hupper := (abs_le.mp (herror index hindex)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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

theorem finite_positive_product_tail (S : Finset ℕ) (f : ℕ → ℝ) {N : ℕ} {K : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hS : ∀ n ∈ S, N < n)
    (hf : ∀ n ∈ S, 0 ≤ f n) (herror : ∀ n ∈ S, |f n - 1| ≤ K / (n : ℝ) ^ 2)
    (hsmall : K / N ≤ 1 / 2) :
    |(∏ n ∈ S, f n) - 1| ≤ 2 * K / N := by
  have hsum : (∑ n ∈ S, K / (n : ℝ) ^ 2) ≤ K / N := by
    have h := mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail S hN hS) hK
    simpa only [Finset.mul_sum, mul_one_div] using h
  have h := positive_prod_sub_one_le_twice_sum S f (fun n => K / (n : ℝ) ^ 2)
    hf (fun _ _ => by positivity) herror (hsum.trans hsmall)
  exact h.trans ((mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_eq (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveFiberProductComparison
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {I Z : Type*} [Fintype I]

theorem fiberMean_mul_bounds_of_abs_sub_one_le
    (law : FiniteProbabilityWeights I) (gridPoint : I → Z) (z : Z)
    (V δ : ℝ) (hV : 0 ≤ V) (base omitted : I → ℝ)
    (hbase : ∀ i, 0 ≤ base i) (homitted : ∀ i, |omitted i - 1| ≤ δ) :
    (1 - δ) * (V * law.fiberMean gridPoint z base) ≤
        V * law.fiberMean gridPoint z (fun i => base i * omitted i) ∧
      V * law.fiberMean gridPoint z (fun i => base i * omitted i) ≤
        (1 + δ) * (V * law.fiberMean gridPoint z base) := by
  classical
  have hpoint (i : I) :
      (1 - δ) * base i ≤ base i * omitted i ∧
        base i * omitted i ≤ (1 + δ) * base i := by
    have herr := abs_le.mp (homitted i)
    constructor
    · have hlow : 1 - δ ≤ omitted i := by linarith [herr.1]
      simpa only [mul_comm (base i)] using mul_le_mul_of_nonneg_right hlow (hbase i)
    · have hupp : omitted i ≤ 1 + δ := by linarith [herr.2]
      simpa only [mul_comm (base i)] using mul_le_mul_of_nonneg_right hupp (hbase i)
  have hlower : (1 - δ) * law.fiberMean gridPoint z base ≤
      law.fiberMean gridPoint z (fun i => base i * omitted i) := by
    unfold fiberMean
    rw [← law.mean_const_mul]
    apply law.mean_mono
    intro i
    by_cases hi : gridPoint i = z
    · simpa only [hi, ite_true] using (hpoint i).1
    · simp only [hi, ite_false, mul_zero, le_refl]
  have hupper : law.fiberMean gridPoint z (fun i => base i * omitted i) ≤
      (1 + δ) * law.fiberMean gridPoint z base := by
    unfold fiberMean
    rw [← law.mean_const_mul]
    apply law.mean_mono
    intro i
    by_cases hi : gridPoint i = z
    · simpa only [hi, ite_true] using (hpoint i).2
    · simp only [hi, ite_false, mul_zero, le_refl]
  constructor
  · simpa only [mul_left_comm V (1 - δ)] using
      mul_le_mul_of_nonneg_left hlower hV
  · simpa only [mul_left_comm V (1 + δ)] using
      mul_le_mul_of_nonneg_left hupper hV

theorem fiberMean_prod_bounds_of_omitted_prod_sub_one_le
    {L : Type*} [Fintype L] [DecidableEq L]
    (law : FiniteProbabilityWeights I) (gridPoint : I → Z) (z : Z)
    (V δ : ℝ) (hV : 0 ≤ V) (_hδ : 0 ≤ δ)
    (retained : Finset L) (f : I → L → ℝ)
    (hf : ∀ i l, 0 ≤ f i l)
    (homitted : ∀ i, |(∏ l ∈ Finset.univ \ retained, f i l) - 1| ≤ δ) :
    (1 - δ) * (V * law.fiberMean gridPoint z (fun i => ∏ l ∈ retained, f i l)) ≤
        V * law.fiberMean gridPoint z (fun i => ∏ l, f i l) ∧
      V * law.fiberMean gridPoint z (fun i => ∏ l, f i l) ≤
        (1 + δ) * (V * law.fiberMean gridPoint z (fun i => ∏ l ∈ retained, f i l)) := by
  have hsplit (i : I) : (∏ l ∈ retained, f i l) *
      (∏ l ∈ Finset.univ \ retained, f i l) = ∏ l, f i l := by
    simpa only [Finset.compl_eq_univ_sdiff] using
      Finset.prod_mul_prod_compl retained (f i)
  simpa only [hsplit] using
    law.fiberMean_mul_bounds_of_abs_sub_one_le gridPoint z V δ hV
      (fun i => ∏ l ∈ retained, f i l)
      (fun i => ∏ l ∈ Finset.univ \ retained, f i l)
      (fun i => Finset.prod_nonneg (fun l _ => hf i l)) homitted

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TaggedZModOrderBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem taggedIntegerResidue_surjective {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    Function.Surjective (taggedIntegerResidue J N) := by
  intro y
  choose x hx using fun s : Sigma J => ZMod.intCast_surjective (y s.1 s.2)
  exact ⟨x, funext fun h => funext fun j => hx ⟨h, j⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ) (P : MvPolynomial V R) :
    map φ (homogeneousComponent d P) = homogeneousComponent d (map φ P) := by
  ext e
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

theorem crtInput_integerPolynomial_eval (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) (l : L) :
    ZMod.prodEquivPi q hq
      (MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ k, q k))) (crtInput q hq x) F) l =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) F := by
  let e := ZMod.prodEquivPi q hq
  let φ := (Pi.evalRingHom (fun k => ZMod (q k)) l).comp e.toRingHom
  change φ (MvPolynomial.eval₂ _ _ F) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : φ.comp (Int.castRingHom (ZMod (∏ k, q k))) =
      Int.castRingHom (ZMod (q l)) := Subsingleton.elim _ _
  rw [hc]
  congr 1
  funext v
  exact congrFun (e.apply_symm_apply (fun k => x k v)) l

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialTranslate u P) =
      polynomialTranslate (fun i => φ (u i)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, polynomialTranslate_X, map_add, map_C, hP]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem map_integerPolynomial_homogeneousComponent
    {V : Type*} (p A B d : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : MvPolynomial V ℤ) :
    map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent d (map (Int.castRingHom (ZMod (p ^ A))) F)) =
      map (Int.castRingHom (ZMod (p ^ B))) (homogeneousComponent d F) := by
  have hcomp : (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))).comp
      (Int.castRingHom (ZMod (p ^ A))) = Int.castRingHom (ZMod (p ^ B)) :=
    RingHom.eq_intCast' _
  rw [← map_homogeneousComponent, MvPolynomial.map_map, hcomp]

theorem primePowerHomogeneousRankProbability_integerPolynomial
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) :
    primePowerHomogeneousRankProbability p A B n hBA
      (fun i => map (Int.castRingHom (ZMod (p ^ A))) (F i)) row =
      integerPolynomialRankProbability p B n F row := by
  unfold primePowerHomogeneousRankProbability integerPolynomialRankProbability
  have hF : (fun i => map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent (n + 1) (map (Int.castRingHom (ZMod (p ^ A))) (F i)))) =
      (fun i => map (Int.castRingHom (ZMod (p ^ B)))
        (homogeneousComponent (n + 1) (F i))) := by
    funext i
    exact map_integerPolynomial_homogeneousComponent p A B (n + 1) hBA (F i)
  rw [hF]

end Erdos3


namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_not_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) {a : ℕ}
    (ha : largestTestedBadDepth A bad p x < a) (hA : a ≤ A p) : ¬ bad p a x := by
  intro hbad
  have hmem : a ∈ (Finset.Icc 1 (A p)).filter (fun a => bad p a x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hA⟩, hbad⟩
  exact (not_le_of_gt ha) (Finset.le_sup (f := id) hmem)

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularBoundedCoefficientPolynomial_degree {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) :
    (modularBoundedCoefficientPolynomial h c).totalDegree ≤ h := by
  unfold modularBoundedCoefficientPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (c e)).trans e.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteUnchargedPrimeDensity
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem finite_prime_depth_mass {p : ℕ} (hp : 2 ≤ p) (A : ℕ) :
    (∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2) ≤ 2 / (p : ℝ) ^ 2 := by
  let r : ℝ := 1 / (p : ℝ) ^ 2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r ≤ 1 / 2 := by
    dsimp only [r]
    apply (div_le_div_iff₀ (pow_pos hp0 2) (by norm_num)).mpr
    nlinarith
  calc
    _ = r * ∑ a ∈ Finset.range A, r ^ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [r]
      simp only [one_div, inv_pow]
      rw [pow_right_comm, pow_succ' _ a, mul_inv]
    _ ≤ r * ∑ a ∈ Finset.range A, (1 / (2 : ℝ)) ^ a := by
      apply mul_le_mul_of_nonneg_left _ hr0
      exact Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ hr0 hr a)
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le A) hr0
    _ = _ := by dsimp only [r]; ring

theorem finiteCharacter_order_dvd_of_annihilation {H : Type*} [AddCommGroup H]
    (N : ℕ) (hN : ∀ x : H, N • x = 0) (χ : AddChar H ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hN x]
  exact χ.map_zero_eq_one

theorem finiteCharacter_uncharged_prime_mass {I H : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (f : AddChar H ℂ → ℝ)
    (hdecay : ∀ χ, χ ≠ 1 → f χ ≤ 1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) :
    (∑ χ : AddChar H ℂ with χ ≠ 1, f χ) ≤ 2 / (p : ℝ) ^ 2 := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => χ ≠ 1)
  let orders := (Finset.range A).image (fun a => p ^ (a + 1))
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf orders := by
    intro χ hχ
    obtain ⟨a, ha, heq⟩ := (Nat.dvd_prime_pow hp).mp
      (finiteCharacter_order_dvd_of_annihilation (p ^ A) hann χ)
    have ha0 : 0 < a := by
      by_contra hz
      have haZ : a = 0 := by omega
      have ho : orderOf χ = 1 := by simpa only [haZ, pow_zero] using heq
      exact (Finset.mem_filter.mp hχ).2 (orderOf_eq_one_iff.mp ho)
    exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega),
      by rw [Nat.sub_add_cancel ha0]; exact heq.symm⟩
  change (∑ χ ∈ S, f χ) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  have hinner (q : ℕ) (hq : q ∈ orders) :
      (∑ χ ∈ S with orderOf χ = q, f χ) ≤ 1 / (q : ℝ) ^ 2 := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
    have hq0 : 0 < p ^ (a + 1) := pow_pos hp.pos _
    have hqR : (0 : ℝ) < ((p ^ (a + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hq0
    have hc : (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card ≤
        (p ^ (a + 1)) ^ Fintype.card I :=
      (Finset.card_le_card (by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩)).trans
          (finiteCharacter_exactOrder_card_le π hπ _ hq0)
    calc
      _ ≤ ∑ _χ ∈ S with orderOf _χ = p ^ (a + 1),
          1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2) := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa only [(Finset.mem_filter.mp hχ).2] using
          hdecay χ (Finset.mem_filter.mp (Finset.mem_filter.mp hχ).1).2
      _ = (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p ^ (a + 1) : ℕ) : ℝ) ^ Fintype.card I *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = _ := by
        rw [pow_add (((p ^ (a + 1) : ℕ) : ℝ)) (Fintype.card I) 2]
        field_simp
  calc
    _ ≤ ∑ q ∈ orders, 1 / (q : ℝ) ^ 2 := Finset.sum_le_sum hinner
    _ = ∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2 := by
      rw [Finset.sum_image]
      · simp only [Nat.cast_pow]
      · intro a _ b _ hab
        exact Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hab)
    _ ≤ _ := finite_prime_depth_mass hp.two_le A

theorem finiteImage_uncharged_prime_density {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have he := finiteImageFourier_truncation w Y {1} z (Nat.cast_nonneg (Fintype.card H))
  have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Complex.ofReal_natCast, div_self hcard, div_self hcardC, one_mul,
    Finset.sum_singleton, finiteImageCharacteristic, AddChar.one_apply,
    FiniteProbabilityWeights.complexMean_const, star_one, mul_one] at he
  have htail := finiteCharacter_uncharged_prime_mass π hπ hp hann _ hdecay
  have htail' : spectrumTail {1} (fun χ => ‖finiteImageCharacteristic w Y χ‖) ≤ 2 / (p : ℝ) ^ 2 := by
    simpa only [spectrumTail, Finset.mem_singleton, Finset.sum_filter, ite_not] using htail
  have hbound := he.trans htail'
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound

theorem finiteImage_uncharged_prime_density_rpow {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H) {P : ℝ}
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      (orderOf χ : ℝ) ^ (-P)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have hfull (χ : AddChar H ℂ) : ‖finiteImageCharacteristic w Y χ‖ ≤
      1 * (orderOf χ : ℝ) ^ (-P) := by
    by_cases hχ : χ = 1
    · subst χ
      simp only [finiteImageCharacteristic, AddChar.one_apply,
        FiniteProbabilityWeights.complexMean_const, norm_one, orderOf_one,
        Nat.cast_one, Real.one_rpow, mul_one, le_refl]
    · simpa only [one_mul] using hdecay χ hχ
  have hinteger := finiteCharacter_integer_decay_of_rpow (I := I)
    (show (0 : ℝ) ≤ 1 by norm_num) hP _ hfull
  exact finiteImage_uncharged_prime_density π hπ hp hann w Y (fun χ _ => hinteger χ) z

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

theorem rationalOutputDensity_nonneg {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : 0 ≤ rationalOutputDensity p Y N b := by
  unfold rationalOutputDensity finiteImageMass
  exact mul_nonneg (Nat.cast_nonneg _) (p.mean_nonneg (fun _ => by split_ifs <;> norm_num))

theorem rationalOutputDensity_fourier {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) :
    (rationalOutputDensity p Y N b : ℂ) =
      ∑ χ : AddChar (J → ZMod N) ℂ,
        finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b) := by
  simpa only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast] using
    (finiteImageFourier_inversion p (fun x j => (Y x j : ZMod N)) b).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

omit [Fintype V] in

theorem crtPrimePowerIntegerPolynomialOutput_reduce {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) [NeZero (∏ l, p l ^ A l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) :
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l)) =
      crtPrimePowerPolynomialMap p A e hq F r x j.1 j.2 := by
  unfold crtPrimePowerIntegerPolynomialOutput crtPrimePowerPolynomialMap
  change (Int.castRingHom (ZMod (∏ l, p l ^ A l))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem finiteImageMass_outputEquiv {X Z W : Type*} [Fintype X]
    [DecidableEq Z] [DecidableEq W] (law : FiniteProbabilityWeights X)
    (Y : X → Z) (e : Z ≃ W) (z : Z) :
    finiteImageMass law (fun x => e (Y x)) (e z) = finiteImageMass law Y z := by
  unfold finiteImageMass
  simp only [e.injective.eq_iff]

theorem crt_integer_polynomial_rational_density_product
    {L V : Type*} [Fintype L] [Fintype V] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (r : ∀ l, V → ZMod (p l ^ A l))
    (z : Sigma J → ZMod (∏ l, p l ^ A l)) :
    let : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalOutputDensity (crtPrimePowerPolynomialLaw (V := V) p A)
      (crtPrimePowerIntegerPolynomialOutput p A e hq F r) (∏ l, p l ^ A l) z =
      ∏ l, rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
        (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l)) (p l ^ A l)
        (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
          (Finset.mem_univ l)) (ZMod (p l ^ A l)) (z j)) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  let outputEquiv : (Sigma J → ZMod (∏ l, p l ^ A l)) ≃
      (∀ l, Sigma J → ZMod (p l ^ A l)) :=
    (taggedPolynomialOutputCurry J _).toEquiv |>.trans
      ((taggedOutputCRTEquiv J (fun l => p l ^ A l) hq).toEquiv.trans
        (Equiv.piCongrRight (fun l => (taggedPolynomialOutputCurry J (p l ^ A l)).symm.toEquiv)))
  let localLaw := fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l))
  let Y := fun (l : L) (x : V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l) x j : ZMod (p l ^ A l))
  let globalY := fun (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l))
  have heval (x : ∀ l, V → ZMod (p l ^ A l)) :
      outputEquiv (globalY x) = fun l => Y l (x l) := by
    funext l j
    change ZMod.prodEquivPi (fun l => p l ^ A l) hq (globalY x j) l = Y l (x l) j
    dsimp only [globalY, Y]
    rw [crtPrimePowerIntegerPolynomialOutput_reduce,
      localPrimePowerIntegerPolynomialOutput_reduce]
    exact crtInput_integerPolynomial_eval (fun l => p l ^ A l) hq (F j.1 j.2)
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) l
  have hmass : finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z =
      ∏ l, finiteImageMass (localLaw l) (Y l) (outputEquiv z l) := by
    rw [← finiteImageMass_outputEquiv _ globalY outputEquiv z]
    simp_rw [heval]
    exact finiteImageMass_pi localLaw Y (outputEquiv z)
  have hcard : Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) =
      ∏ l, Fintype.card (Sigma J → ZMod (p l ^ A l)) :=
    (Fintype.card_congr outputEquiv).trans Fintype.card_pi
  change (Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) : ℝ) *
      finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z = _
  rw [hmass, hcard, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  unfold rationalOutputDensity
  congr 1
  apply congrArg (finiteImageMass (localLaw l) (Y l))
  funext j
  exact ZMod.prodEquivPi_apply (fun l => p l ^ A l) hq (z j) l

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

attribute [local instance] OAI.Erdos3.crtInputModulusNeZero
theorem crtPolynomialInputLaw_complexMean
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (f : (V → ZMod (∏ l, p l ^ A l)) → ℂ) :
    (crtPolynomialInputLaw p A e hq origin).complexMean f =
      (crtPrimePowerPolynomialLaw (V := V) p A).complexMean
        (fun x => f (prescribedCRTPolynomialInput p A e hq origin x)) :=
  FiniteProbabilityWeights.fiberLaw_complexMean _ _ _

theorem crtPolynomialInputLaw_integerLong_characteristic
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (MvPolynomial.eval
        (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
          inactive) (poly j) : ZMod (∏ l, p l ^ A l))) χ :=
  crtPolynomialInputLaw_complexMean p A e hq origin _

theorem crtPolynomialInputLaw_integerLong_characteristic_of_output
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (Y : (∀ l, V → ZMod (p l ^ A l)) → Out → ℤ)
    (hY : ∀ x j, Y x j = MvPolynomial.eval
      (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
        inactive) (poly j))
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (Y x j : ZMod (∏ l, p l ^ A l))) χ := by
  rw [crtPolynomialInputLaw_integerLong_characteristic]
  apply congrArg (fun F => finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A) F χ)
  funext x j
  rw [hY]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem samplerLongEmbedding_dedicated_mem_range (inactive : D → Prop) (h : D → ℕ)
    (d : D) (b : B d) (v : Fin (h d)) :
    (Sum.inr ⟨d, b, v⟩ : SamplerTupleIndex G B h) ∈
      Set.range (samplerLongEmbedding inactive h) ↔ ¬ inactive d := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with g | ⟨a, c, w⟩
    · simp only [samplerLongEmbedding_common, Sum.inl_ne_inr] at hk
    · have he : a.val = d := congrArg Sigma.fst (Sum.inr.inj hk)
      exact he ▸ a.property
  · intro hd
    exact ⟨.inr ⟨⟨d, hd⟩, b, v⟩, rfl⟩

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

theorem homogeneousComponent_map_ringHom (f : R →+* S) (h : ℕ) (P : MvPolynomial K R) :
    homogeneousComponent h (P.map f) = (homogeneousComponent h P).map f := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

theorem modularBoundedCoefficientPolynomial_map [Fintype K]
    (f : R →+* S) (h : ℕ) (c : BoundedCoefficientExponent K h → R) :
    modularBoundedCoefficientPolynomial h (fun e => f (c e)) =
      (modularBoundedCoefficientPolynomial h c).map f := by
  simp only [modularBoundedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

end RingMap

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedCongruenceModulusBad_good (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (hgood : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w ≤ (N : ℝ) ^ (-C) :=
  le_of_not_gt (fun hbad => hgood ⟨v, j, w, hw, hbad⟩)

theorem allocatedCongruenceRankBad_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)
    (p : P) (a : ℕ) (x : AllocatedCongruenceScalarIndex X E inactive L → ℤ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a x)
    (v : LayerSamplerVariables G I n B → ZMod (p.val ^ a)) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p.val ^ a)))
      (fun j q i => (r j q i : ZMod (p.val ^ a)))
      (fun b q => (projection j b q : ZMod (p.val ^ a)))
      spatial (kernel j) (block j) (fun o l => (x ⟨j,(o,l)⟩ : ZMod (p.val ^ a))) v w ≤
        ((p.val ^ a : ℕ) : ℝ) ^ (-C) := by
  have hmod : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
      C (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) :=
    fun hbad => hgood ⟨p.property, hbad⟩
  exact allocatedCongruenceModulusBad_good inactive noise r projection spatial kernel block C
    (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) hmod v j w hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ConditionPolynomialMapDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R S : Type*} [CommRing R] [CommRing S]

theorem conditionPolynomial_totalDegree_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) :
    (conditionPolynomial f hf v P).totalDegree ≤ P.totalDegree := by
  let u : I → R := fun i => if i ∈ Set.range f then 0 else v i
  have ht : polynomialTranslate u P ∈ weightedSupportLE (1 : I → ℕ) P.totalDegree := by
    apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ)
      (fun i => X i + C (u i))
    · intro i
      exact (weightedSupportLE (1 : I → ℕ) 1).add_mem
        (weightedSupportLE_X _ i) (weightedSupportLE_C _ _ _)
    · exact (mem_weightedSupportLE_one_iff P _).mpr le_rfl
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro a ha
  change a ∈ (conditionPolynomial f hf v P).support at ha
  have hmem : a.mapDomain f ∈ (polynomialTranslate u P).support := by
    simpa only [conditionPolynomial, u, mem_support_iff, coeff_killCompl] using ha
  have h : Finsupp.weight (fun _ : I => 1) (a.mapDomain f) ≤ P.totalDegree := ht hmem
  change Finsupp.weight (fun _ : J => 1) a ≤ P.totalDegree
  simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

theorem conditionPolynomial_map (φ : R →+* S) (f : J → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R) :
    map φ (conditionPolynomial f hf v P) =
      conditionPolynomial f hf (fun i => φ (v i)) (map φ P) := by
  unfold conditionPolynomial
  rw [← killCompl_map, polynomialTranslate_map_coefficients]
  apply congrArg (fun u : I → S => killCompl hf (polynomialTranslate u (map φ P)))
  funext i
  split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedCongruenceIntegerPolynomial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o).totalDegree ≤
      j.val + 1 := by
  rcases o with x | i | a
  · apply (conditionPolynomial_totalDegree_le _ _ _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le
    · rw [totalDegree_C]
      exact Nat.zero_le _
    · exact (spatialRankPolynomial_degree _).trans (by omega)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)

theorem allocatedCongruenceIntegerPolynomial_top_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedOriginalTaggedTop inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        (fun k => (v k : ZMod N)) (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [← homogeneousComponent_map_ringHom]
  rcases o with x | i | a
  · have hx : j.val + 1 = 1 := by simp only [x.property, zero_add]
    simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hx,
      map_add, map_C, Int.coe_castRingHom]
    have hs : (spatialRankPolynomial (fun d => noise (d, x.val))).map
        (Int.castRingHom (ZMod N)) =
        spatialRankPolynomial (fun d => (noise (d, x.val) : ZMod N)) := by
      simp only [spatialRankPolynomial, map_sum, MvPolynomial.map_monomial,
        Int.coe_castRingHom]
    rw [hs]
    simp only [conditionPolynomial, map_add, polynomialTranslate_C, killCompl_C]
    have hc : homogeneousComponent 1 (C (base x.val : ZMod N) :
        MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)) = 0 :=
      homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; exact zero_lt_one)
    rw [hc, zero_add]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop,
      modularDeckPolynomial, ← modularBoundedCoefficientPolynomial_map,
      Int.coe_castRingHom]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop,
      ← modularBoundedCoefficientPolynomial_map, Int.coe_castRingHom,
      allocatedCongruenceIntegerEmbedding]
    rfl

theorem allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedCongruenceRankPolynomial inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        spatial kernel block
        (fun z => allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
          spatial kernel block (allocatedCongruenceOutputEmbedding inactive j z))
        (fun k => (v k : ZMod N)) o := by
  rw [allocatedCongruenceRankPolynomial_original]
  exact allocatedCongruenceIntegerPolynomial_top_reduce N inactive j base noise r projection v o

end Erdos3.VectorPolynomial

end

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

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

theorem allocatedCongruenceIntegerPolynomial_rank_probability
    (p a : ℕ) [NeZero p] (base : X → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a)) :
    integerPolynomialRankProbability p a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w =
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p ^ a)))
      (fun j q i => (r j q i : ZMod (p ^ a)))
      (fun b q => (projection j b q : ZMod (p ^ a))) spatial (kernel j) (block j)
      (fun o l => (selected ⟨j,(o,l)⟩ : ZMod (p ^ a))) (fun k => (v k : ZMod (p ^ a))) w := by
  unfold integerPolynomialRankProbability allocatedCongruenceRankFailureProbability
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
      (p ^ a) inactive j base noise r (projection j) spatial (kernel j) (block j)]
  simp only [polynomialCharacterRow, smul_eq_C_mul]

theorem allocatedCongruenceIntegerPolynomial_rank_of_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p : P) (a : ℕ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    integerPolynomialRankProbability p.val a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w ≤
      (p.val : ℝ) ^ (-C * a) := by
  rw [allocatedCongruenceIntegerPolynomial_rank_probability inactive noise r projection spatial kernel block]
  have h := allocatedCongruenceRankBad_good inactive noise r projection spatial kernel block
    P C p a selected hgood (fun k => (v k : ZMod (p.val ^ a))) j w hw
  calc
    _ ≤ ((p.val ^ a : ℕ) : ℝ) ^ (-C) := h
    _ = (p.val : ℝ) ^ (-C * a) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p.val)]
      congr 1
      ring

theorem allocatedCongruence_largest_bad_depth_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (p : P) (a : ℕ)
    (ha : largestTestedBadDepth A
      (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C)
      p.val selected < a) (hA : a ≤ A p.val) :
    ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected :=
  largestTestedBadDepth_not_bad A _ p.val selected ha hA

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

theorem samplerSeparatedValues_eq_extend {R : Type*} [Zero R]
    (inactive : D → Prop) (h : D → ℕ)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    Sum.elim long raw ∘ samplerSeparatedVariable inactive h =
      Function.extend (samplerLongEmbedding inactive h) long (samplerFrozenRaw h raw) := by
  funext k
  rcases k with g | ⟨d, b, v⟩
  · exact ((samplerLongEmbedding (B := B) inactive h).injective.extend_apply
      long (samplerFrozenRaw h raw) (.inl g)).symm
  · by_cases hd : inactive d
    · have hn : ¬ ∃ k, samplerLongEmbedding (G := G) inactive h k = .inr ⟨d, b, v⟩ := by
        intro hk
        exact ((samplerLongEmbedding_dedicated_mem_range inactive h d b v).mp hk) hd
      rw [Function.extend_apply' long (samplerFrozenRaw h raw) _ hn]
      simp only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h d b v hd,
        Sum.elim_inr, samplerFrozenRaw]
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h d b v hd,
        Sum.elim_inl]
      exact ((samplerLongEmbedding (G := G) inactive h).injective.extend_apply
        long (samplerFrozenRaw h raw) (.inr ⟨⟨d, hd⟩, b, v⟩)).symm

theorem eval_rename_samplerSeparatedVariable {R : Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (P : MvPolynomial (SamplerTupleIndex G B h) R)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    eval (Sum.elim long raw) (rename (samplerSeparatedVariable inactive h) P) =
      eval long (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective (samplerFrozenRaw h raw) P) := by
  rw [eval_rename, samplerSeparatedValues_eq_extend, eval_conditionPolynomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j)

theorem allocatedUnconditionedCongruenceIntegerPolynomial_condition
    (v : LayerSamplerVariables G I n B → ℤ) :
    conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
      (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o) =
      allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o := by
  rcases o with x | i | a <;> rfl

theorem allocatedSeparatedCongruencePolynomial_eval
    (long : LayerSamplerLongVariables inactive G B → ℤ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ) :
    MvPolynomial.eval (Sum.elim long raw)
      (allocatedSeparatedCongruencePolynomial inactive j base noise r projection o) =
      MvPolynomial.eval long (allocatedCongruenceIntegerPolynomial inactive j base noise r projection
        (samplerFrozenRaw (layerSamplerDegree I n) raw) o) := by
  rw [allocatedSeparatedCongruencePolynomial, eval_rename_samplerSeparatedVariable]
  rw [← allocatedUnconditionedCongruenceIntegerPolynomial_condition]
  rfl

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

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

attribute [local instance] OAI.Erdos3.VectorPolynomial.forecastProductModulusNeZero
theorem allocatedForecastPolynomial_rational_density_eq_crt
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod (∏ p : Pr, p.val ^ A p.val)) :
    letI : DecidableEq Pr := Classical.decEq _
    let hq := primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective
    rationalOutputDensity
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq origin)
      (integerLongPolynomialOutput (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val)) (∏ p : Pr, p.val ^ A p.val) β =
    rationalOutputDensity
      (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : Pr => p.val) (fun p : Pr => A p.val))
      (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
          (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
      (∏ p : Pr, p.val ^ A p.val) β := by
  let : DecidableEq Pr := Classical.decEq _
  intro hq
  apply Complex.ofReal_injective
  rw [rationalOutputDensity_fourier, rationalOutputDensity_fourier]
  apply Finset.sum_congr rfl
  intro χ _
  congr 1
  exact crtPolynomialInputLaw_integerLong_characteristic_of_output
    (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val) hq origin
    (allocatedForecastPolynomial inactive base noise r projection) raw
    (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p : Pr => e p.val) hq
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
    (fun x j => by
      simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
        allocatedForecastPolynomial] using
        (allocatedSeparatedCongruencePolynomial_eval inactive j.1 base noise r (projection j.1)
          j.2 _ raw).symm) χ

theorem allocatedForecastPolynomial_rational_density_product
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod (∏ p : Pr, p.val ^ A p.val)) :
    letI : DecidableEq Pr := Classical.decEq _
    let hq := primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective
    rationalOutputDensity
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq origin)
      (integerLongPolynomialOutput (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val)) (∏ p : Pr, p.val ^ A p.val) β =
      ∏ p : Pr, rationalOutputDensity
        (FiniteProbabilityWeights.uniform (LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val)))
        (localPrimePowerIntegerPolynomialOutput p.val (A p.val) (e p.val)
          (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
            (samplerFrozenRaw (layerSamplerDegree I n) raw)) (origin p)) (p.val ^ A p.val)
        (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun p : Pr => p.val ^ A p.val)
          (Finset.mem_univ p)) (ZMod (p.val ^ A p.val)) (β j)) := by
  let : DecidableEq Pr := Classical.decEq _
  intro hq
  apply (allocatedForecastPolynomial_rational_density_eq_crt inactive noise r projection
    Pr A e hp base origin raw β).trans
  have h := crt_integer_polynomial_rational_density_product
      (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val) hq
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin β
  convert h using 1 <;> congr 1
  funext p
  congr 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTInactiveDensityGoodPrimeDeletion
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem primePower_integer_polynomial_shifted_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : ∀ j, J j → ZMod (p ^ A)) :
    let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
    let Y := fun (x : V → ZMod (p ^ A)) j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
    |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 ∧
    (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z ≤
      1 + 2 / (p : ℝ) ^ 2 := by
  dsimp only
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) j i =>
    eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
  have hdecay (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (_hχ : χ ≠ 1) :
      ‖finiteImageCharacteristic law Y χ‖ ≤
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hlocal := primePower_polynomial_image_characteristic_decay_s2 hs p A 0 0 hp C hC
      (fun j i => map (Int.castRingHom (ZMod (p ^ A))) (F j i))
      (fun j i => (totalDegree_map_le _ _).trans (hF j i))
      (by
        intro B hB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank B hB hBA j row hunit)
      r χ
    simpa only [law, Y, eval_map, Nat.zero_add, pow_zero, Nat.cast_one, Real.one_rpow,
      one_mul] using hlocal
  have hann (x : ∀ j, J j → ZMod (p ^ A)) : (p ^ A) • x = 0 := by
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have h := finiteImage_uncharged_prime_density_rpow (taggedIntegerResidue J (p ^ A))
    (taggedIntegerResidue_surjective J (p ^ A)) hp hann law Y hP hdecay z
  have hd : |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 := by
    simpa only [← Nat.card_eq_fintype_card] using h
  exact ⟨hd, by linarith [(abs_le.mp hd).2]⟩

theorem localPrimePowerIntegerPolynomialOutput_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : Sigma J → ZMod (p ^ A)) :
    |rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z - 1| ≤
        2 / (p : ℝ) ^ 2 ∧
    rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z ≤
        1 + 2 / (p : ℝ) ^ 2 := by
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput p A 0 F r x j : ZMod (p ^ A))
  let curry := (taggedPolynomialOutputCurry J (p ^ A)).toEquiv
  have hY : (fun x => curry (Y x)) = fun x j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i) := by
    funext x j i
    change (localPrimePowerIntegerPolynomialOutput p A 0 F r x ⟨j, i⟩ : ZMod (p ^ A)) = _
    rw [localPrimePowerIntegerPolynomialOutput_reduce]
    simp only [pow_zero, one_mul]
  have hdensity : rationalOutputDensity law
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z =
      (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law
        (fun x j i => eval₂ (Int.castRingHom (ZMod (p ^ A)))
          (fun v => r v + x v) (F j i)) (curry z) := by
    change (Fintype.card (Sigma J → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z = _
    rw [Fintype.card_congr curry, ← finiteImageMass_outputEquiv law Y curry z, hY]
  rw [hdensity]
  exact primePower_integer_polynomial_shifted_uncharged_density hs p A hp C hC hP
    F hF hrank r (curry z)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem indexed_good_prime_product_tail {L : Type*}
    (p : L → ℕ) (hp : Function.Injective p) (S : Finset L) (f : L → ℝ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hlarge : ∀ l ∈ S, cutoff < p l) (hnonneg : ∀ l ∈ S, 0 ≤ f l)
    (herror : ∀ l ∈ S, |f l - 1| ≤ 2 / (p l : ℝ) ^ 2) :
    |(∏ l ∈ S, f l) - 1| ≤ 4 / (cutoff : ℝ) := by
  have h := finite_positive_product_tail (S.image p) (Function.extend p f (fun _ => 1))
    hcutoff (by norm_num : (0 : ℝ) ≤ 2)
    (by rintro q hq; obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq; exact hlarge l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using hnonneg l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using herror l hl) hsmall
  simpa only [Finset.prod_image hp.injOn, hp.extend_apply, show (2 : ℝ) * 2 = 4 by norm_num] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
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
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem localReference_degree
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j) :
    (path.localReferencePolynomial raw j o).totalDegree ≤ j.val + 1 :=
  allocatedCongruenceIntegerPolynomial_degree (allocatedShortAxis (I := I) U b S.value)
    j path.base path.noise (allocatedReadDeck path.read)
    (fun a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (samplerFrozenRaw (layerSamplerDegree I n) raw) o

omit [Fintype Tsp] in

theorem localReference_rank
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (a : ℕ) (ha : path.referenceBadDepth p.val < a)
    (hA : a ≤ path.exponent p.val) (j : Fin m)
    (row : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
    (hunit : ∃ o, IsUnit (row o)) :
    letI := path.primeNeZero
    integerPolynomialRankProbability p.val a j.val
      (path.localReferencePolynomial raw j) row ≤
      (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) := by
  let := path.primeNeZero
  exact allocatedCongruenceIntegerPolynomial_rank_of_good
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    spatial kernel block path.primes (modularForecastRankConstant m Dmod : ℝ) p a
    (allocatedCongruence_largest_bad_depth_good
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
      spatial kernel block path.primes path.exponent
      (modularForecastRankConstant m Dmod : ℝ) p a ha hA)
    path.base (samplerFrozenRaw (layerSamplerDegree I n) raw) j row hunit

omit [Fintype Tsp] in

theorem localReference_uncharged_density
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (hbad : path.referenceBadDepth p.val = 0)
    (hpres : path.prescribed p.val = 0)
    (z : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (p.val ^ path.exponent p.val)) :
    letI := path.primeNeZero
    let density := rationalOutputDensity
      (FiniteProbabilityWeights.uniform
        (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
          ZMod (p.val ^ path.exponent p.val)))
      (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
        (path.localReferencePolynomial raw) (path.origin p))
      (p.val ^ path.exponent p.val) z
    |density - 1| ≤ 2 / (p.val : ℝ) ^ 2 ∧ density ≤ 1 + 2 / (p.val : ℝ) ^ 2 := by
  let := path.primeNeZero
  have hdim :
      ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) hm Dmod hD
  have hrank (a : ℕ) (ha : 0 < a) (hA : a ≤ path.exponent p.val) (j : Fin m)
      (row : AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
      (hunit : ∃ o, IsUnit (row o)) :
      integerPolynomialRankProbability p.val a j.val (path.localReferencePolynomial raw j) row ≤
        (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) :=
    path.localReference_rank raw p a (by simpa only [hbad] using ha) hA j row hunit
  have hdensity := localPrimePowerIntegerPolynomialOutput_uncharged_density hm p.val
    (path.exponent p.val) (path.prime p.val p.property)
    (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) hdim
    (path.localReferencePolynomial raw) (path.localReference_degree raw) hrank (path.origin p) z
  simpa only [hpres, rationalOutputDensity, ← Nat.card_eq_fintype_card] using hdensity

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
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
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceModulusNeZero
omit [Fintype Tsp] in
theorem referenceRetainedPrimes_omitted (cutoff : ℕ) (p : path.primes)
    (hp : p ∉ path.referenceRetainedPrimes cutoff) :
    cutoff < p.val ∧ path.referenceBadDepth p.val = 0 ∧ path.prescribed p.val = 0 := by
  simp only [referenceRetainedPrimes, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] at hp
  exact ⟨Nat.lt_of_not_ge hp.2.2, hp.1, hp.2.1⟩

omit [Fintype Tsp] in
theorem referenceLocalDensity_nonneg
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus)
    (p : path.primes) : 0 ≤ path.referenceLocalDensity raw β p :=
  rationalOutputDensity_nonneg _ _ _ _

omit [Fintype Tsp] in

theorem reference_rational_density_product
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    rationalOutputDensity path.referenceInputLaw
      (integerLongPolynomialOutput path.referencePolynomial raw path.referenceModulus)
      path.referenceModulus β = ∏ p : path.primes, path.referenceLocalDensity raw β p := by
  dsimp only [referenceInputLaw, referenceLocalDensity, referencePolynomial,
    localReferencePolynomial, referenceModulus]
  have h := allocatedForecastPolynomial_rational_density_product
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    path.primes path.exponent path.prescribed path.prime path.base path.origin raw β
  simp only [rationalOutputDensity, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

omit [Fintype Tsp] in
theorem reference_inactive_density_product {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β =
    gridVolume * inactive.fiberMean gridPoint z
      (fun i => ∏ p : path.primes, path.referenceLocalDensity (raw i) β p) := by
  unfold rationalInactiveForecast
  simp_rw [path.reference_rational_density_product]

omit [Fintype Tsp] in

theorem reference_inactive_goodPrimeDeletion_s2_oai {Ω Z : Type*} [Fintype Ω]
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    let full := rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β
    let truncated := path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  dsimp only
  rw [path.reference_inactive_density_product]
  unfold retainedReferenceForecast
  apply inactive.fiberMean_prod_bounds_of_omitted_prod_sub_one_le gridPoint z
    gridVolume δ hvolume hδ (path.referenceRetainedPrimes cutoff)
    (fun i p => path.referenceLocalDensity (raw i) β p)
    (fun i p => path.referenceLocalDensity_nonneg (raw i) β p)
  intro i
  apply (indexed_good_prime_product_tail (fun p : path.primes => p.val) Subtype.val_injective
    (Finset.univ \ path.referenceRetainedPrimes cutoff)
    (fun p => path.referenceLocalDensity (raw i) β p) cutoff hcutoff hsmall ?_
    (fun p _ => path.referenceLocalDensity_nonneg (raw i) β p) ?_).trans haccuracy
  · intro p hp
    exact (path.referenceRetainedPrimes_omitted cutoff p (Finset.mem_sdiff.mp hp).2).1
  · intro p hp
    obtain ⟨_, hbad, hpres⟩ :=
      path.referenceRetainedPrimes_omitted cutoff p (Finset.mem_sdiff.mp hp).2
    exact (path.localReference_uncharged_density hm hD (raw i) p hbad hpres _).1

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion_s2_oai.{u_1, u_2} := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion_s2_oai.{u_1, u_2}
