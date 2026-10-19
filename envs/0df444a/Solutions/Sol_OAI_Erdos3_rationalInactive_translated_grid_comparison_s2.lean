-- Prove2me | solution 1 for OAI.Erdos3.rationalInactive_translated_grid_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:46.19942+00:00
-- url     : https://prove2.me/submissions/5bf604c4-5c4c-416b-874c-3de8cd131cec

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B161

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTsum
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_zero_of_not_mem_image (F : X → R) (f : X → ℝ)
    (r : R) (hr : r ∉ Finset.univ.image F) : p.fiberMean F r f = 0 := by
  have hne : ∀ x, F x ≠ r := by
    intro x hx
    exact hr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  simp only [fiberMean, hne, ite_false, mean_const]

theorem complexMean_fiber_factor_sum_image (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r ∈ Finset.univ.image F, (p.fiberMean F r f : ℂ) * a r := by
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : F x ∈ Finset.univ.image F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc, hx]

end Erdos3.FiniteProbabilityWeights

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem scaledRectangular_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (c T : J → ℝ) {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, m / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(m ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, f (fun j => (c j + m * z j) / T j)) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have h := rectangularLattice_quadrature f hLip (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hR hδ hδ1 (by simpa only [one_div_div] using hmesh) hsupport
  simp only [rectangularLatticePoint_scaled c T hm.ne', Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ] at h
  have he (v : ℝ) : v / ((∏ j, T j) / m ^ Fintype.card J) =
      (m ^ Fintype.card J / (∏ j, T j)) * v := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem scaledRectangularComplex_summable (f : (J → ℝ) → ℂ) (c T : J → ℝ)
    {q : ℝ} (hq : 0 < q) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (fun z : J → ℤ => f (fun j => (c j + q * z j) / T j)) := by
  have hre := scaledRectangularWeight_summable (fun x => (f x).re) c T hq hT
    (fun x hx => by rw [hsupport x hx, Complex.zero_re])
  have him := scaledRectangularWeight_summable (fun x => (f x).im) c T hq hT
    (fun x hx => by rw [hsupport x hx, Complex.zero_im])
  have h := (Complex.summable_ofReal.mpr hre).add
    ((Complex.summable_ofReal.mpr him).mul_right Complex.I)
  simpa only [Complex.re_add_im] using h

theorem compactBox_complex_integrable (f : (J → ℝ) → ℂ) (hf : Continuous f)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  exact hx (hsupport x hn)

theorem scaledRectangular_complex_quadrature (f : (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (c T : J → ℝ) {q : ℝ} (hq : 0 < q)
    (hT : ∀ j, 0 < T j) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hmesh : ∀ j, q / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    ‖((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        (∑' z : J → ℤ, f (fun j => (c j + q * z j) / T j)) - ∫ x, f x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have hreLip : LipschitzWith L (fun x => (f x).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have himLip : LipschitzWith L (fun x => (f x).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have hre := scaledRectangular_quadrature (fun x => (f x).re) hreLip c T hq hT
    hR hδ hδ1 hmesh (fun x hx => by rw [hsupport x hx, Complex.zero_re])
  have him := scaledRectangular_quadrature (fun x => (f x).im) himLip c T hq hT
    hR hδ hδ1 hmesh (fun x hx => by rw [hsupport x hx, Complex.zero_im])
  have hs := scaledRectangularComplex_summable f c T hq hT hsupport
  have hi := compactBox_complex_integrable f hLip.continuous R hsupport
  have hire : (∫ x, f x).re = ∫ x, (f x).re := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hi).symm
  have hiim : (∫ x, f x).im = ∫ x, (f x).im := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hi).symm
  have h := (Complex.norm_le_abs_re_add_abs_im
    ((((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
      (∑' z : J → ℤ, f (fun j => (c j + q * z j) / T j))) - ∫ x, f x)).trans
    (add_le_add (by simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_tsum hs, hire] using hre)
      (by simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.im_tsum hs, hiim] using him))
  exact h.trans_eq (by ring)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem compactGrid_summable {J : Type*} [Fintype J]
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    Summable (fun k : J → ℤ => g (fun j => ((k j : ℝ) - center j) / scale j)) := by
  have h := rectangularWeight_summable g center scale hscale hsupport
  unfold rectangularWeight rectangularLatticePoint at h
  simpa only [Pi.zero_apply, sub_zero] using h

theorem compactGrid_weighted_summable {J : Type*} [Fintype J]
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) (mask : (J → ℤ) → ℂ) :
    Summable (fun k : J → ℤ => (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * mask k) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rectangularWeightIndices center scale R) ?_).summable
  intro k hk
  have h := rectangularWeight_zero_off_indices g center scale hscale hsupport k hk
  unfold rectangularWeight rectangularLatticePoint at h
  rw [h, Complex.ofReal_zero, zero_mul]

variable {Ω O : Type*} [Fintype Ω] [Fintype O] [DecidableEq O]

theorem rationalOutputOrderTail_norm_le
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T) (b : O → ZMod N) :
    ‖rationalOutputOrderTail p Y N T b‖ ≤ C / T :=
  (rationalOutputDensity_order_bounds p Y N hC hP hdecay T hT).2.2.2 b

theorem rationalOutputOrderTail_weighted_norm_le
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (b : O → ZMod N) (w : ℝ) (hw : 0 ≤ w) (φ : ℂ) (hφ : ‖φ‖ ≤ 1) :
    ‖(w : ℂ) * rationalOutputOrderTail p Y N T b * φ‖ ≤ (C / T) * w := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ w * ‖rationalOutputOrderTail p Y N T b‖ * 1 :=
      mul_le_mul_of_nonneg_left hφ (mul_nonneg hw (norm_nonneg _))
    _ ≤ w * (C / T) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (rationalOutputOrderTail_norm_le p Y N hC hP hdecay T hT b) hw
    _ = _ := mul_comm _ _

theorem rationalOutputOrderTail_weighted_tsum_le {K : Type*}
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (b : K → O → ZMod N) (φ : K → ℂ) (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖∑' k, (w k : ℂ) * rationalOutputOrderTail p Y N T (b k) * φ k‖ ≤
      (C / T) * ∑' k, w k := by
  exact tsum_of_norm_bounded (hws.hasSum.mul_left (C / T)) (fun k =>
    rationalOutputOrderTail_weighted_norm_le p Y N hC hP hdecay T hT
      (b k) (w k) (hw k) (φ k) (hφ k))

theorem rationalOutputOrderTail_grid_le {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : (J → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ)
    (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k‖ / (∏ j, scale j) ≤
      (C / T) * ((∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / scale j)) /
        (∏ j, scale j)) := by
  have hs := compactGrid_summable g center scale hscale R hsupport
  have h := rationalOutputOrderTail_weighted_tsum_le p Y N hC hP hdecay T hT
    (fun k : J → ℤ => g (fun j => ((k j : ℝ) - center j) / scale j)) (fun k => hg _) hs b φ hφ
  have hd : 0 < ∏ j, scale j := Finset.prod_pos (fun j _ => hscale j)
  exact (div_le_div_of_nonneg_right h hd.le).trans_eq (by ring)

theorem rationalOutputOrderTail_normalized_grid_le {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : (J → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ)
    (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖(∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k) / ((∏ j, scale j : ℝ) : ℂ)‖ ≤
      (C / T) * ((∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / scale j)) /
        (∏ j, scale j)) := by
  have hd : 0 < ∏ j, scale j := Finset.prod_pos (fun j _ => hscale j)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le]
  exact rationalOutputOrderTail_grid_le p Y N hC hP hdecay T hT
    g hg center scale hscale R hsupport b φ hφ

theorem rationalOutputOrderTail_mean_integral_le
    {X K : Type*} [MeasurableSpace X] [Fintype K] [Nonempty K]
    (μ : Measure X)
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ)
    (b : K → O → ZMod N) (φ : K → X → ℂ) (hφ : ∀ k x, ‖φ k x‖ ≤ 1) :
    ‖𝔼 k : K, rationalOutputOrderTail p Y N T (b k) *
      ∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤ (C / T) * ∫ x, g x ∂μ := by
  have hnorm (k : K) : ‖∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤ ∫ x, g x ∂μ := by
    apply norm_integral_le_of_norm_le hgi
    filter_upwards [] with x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg x)]
    exact (mul_le_mul_of_nonneg_left (hφ k x) (hg x)).trans_eq (mul_one _)
  have hpoint (k : K) :
      ‖rationalOutputOrderTail p Y N T (b k) * ∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤
        (C / T) * ∫ x, g x ∂μ := by
    rw [norm_mul]
    exact mul_le_mul (rationalOutputOrderTail_norm_le p Y N hC hP hdecay T hT (b k))
      (hnorm k) (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))
  let law := FiniteProbabilityWeights.uniform K
  have h := (law.norm_complexMean_le_mean_norm _).trans (law.mean_mono hpoint)
  simpa only [law, FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.mean_const] using h

theorem rationalOutputOrderTail_grid_difference {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    (T : ℕ) (g : (J → ℝ) → ℝ) (center scale : J → ℝ)
    (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ) :
    let S := Finset.univ.filter (fun χ : AddChar (O → ZMod N) ℂ => orderOf χ ≤ T)
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k) / ((∏ j, scale j : ℝ) : ℂ) =
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      (rationalOutputDensity p Y N (b k) : ℂ) * φ k) / ((∏ j, scale j : ℝ) : ℂ) -
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      (∑ χ ∈ S, finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ *
        star (χ (b k))) * φ k) / ((∏ j, scale j : ℝ) : ℂ) := by
  intro S
  let full := fun k : J → ℤ => (rationalOutputDensity p Y N (b k) : ℂ)
  let trunc := fun k : J → ℤ => ∑ χ ∈ S,
    finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ (b k))
  have hfull : Summable (fun k : J → ℤ =>
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * full k * φ k) := by
    simpa only [mul_assoc] using compactGrid_weighted_summable
      g center scale hscale R hsupport (fun k => full k * φ k)
  have htrunc : Summable (fun k : J → ℤ =>
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * trunc k * φ k) := by
    simpa only [mul_assoc] using compactGrid_weighted_summable
      g center scale hscale R hsupport (fun k => trunc k * φ k)
  rw [← sub_div, ← hfull.tsum_sub htrunc]
  congr 1
  apply tsum_congr
  intro k
  change _ * (full k - trunc k) * φ k = _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem uniform_fiberLaw_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) :
    (FiniteProbabilityWeights.uniform G).fiberLaw f =
      FiniteProbabilityWeights.uniform H := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro y
  have hh := uniform_mean_surjective_hom_fiber f hf y
  change _ = (Fintype.card H : ℝ)⁻¹
  convert hh using 1
  unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
  congr 1

theorem uniform_complexMean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℂ) :
    (FiniteProbabilityWeights.uniform G).complexMean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).complexMean g := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    uniform_fiberLaw_surjective_hom f hf]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalCharacterIndividualModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {O : Type*} {N : ℕ}

variable [NeZero N] (qW : ℕ) [NeZero qW] (χ : AddChar (O → ZMod N) ℂ)

theorem rationalCharacterIndividualModulus_le_mul {T : ℕ} (hχ : orderOf χ ≤ T) :
    rationalCharacterIndividualModulus qW χ ≤ qW * T := by
  exact (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos qW) (zmod_character_order_pos χ))
    (Nat.lcm_dvd_mul qW (orderOf χ))).trans (Nat.mul_le_mul_left qW hχ)

variable (hW : qW ∣ N)

theorem rationalCharacterIndividualReduction_apply (b : O → ZMod N) :
    rationalCharacterIndividualReduction qW χ hW
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) b) = χ b :=
  congrArg (fun ψ : AddChar (O → ZMod N) ℂ => ψ b)
    (exists_rationalCharacterIndividualReduction qW χ hW).choose_spec.1

omit [NeZero N] [NeZero qW] in
theorem rationalCharacterIndividualModulus_reduce_test {D : Type*} (b : D → ZMod N) :
    zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ)
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) b) =
      zmodPiReduction hW b := by
  funext o
  exact RingHom.congr_fun (ZMod.castHom_comp
    (rationalCharacterIndividualModulus_test_dvd qW χ)
    (rationalCharacterIndividualModulus_dvd qW χ hW)) (b o)

variable [Fintype O]

section Partial

variable {Aux D : Type*} [Fintype D]
variable (χ' : AddChar ((Aux ⊕ D) → ZMod N) ℂ)

theorem rationalCharacterIndividualReduction_partial_phase_uniform
    (aux : Aux → ZMod N) (phase : ℂ → ℂ) (test : (D → ZMod qW) → ℂ) :
    (𝔼 b : D → ZMod N, phase (χ' (Sum.elim aux b)) * test (zmodPiReduction hW b)) =
      𝔼 b : D → ZMod (rationalCharacterIndividualModulus qW χ'),
        phase (rationalCharacterIndividualReduction qW χ' hW
          (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
            test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b) := by
  have hphase (b : D → ZMod N) :
      rationalCharacterIndividualReduction qW χ' hW
        (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux)
          (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) b)) =
        χ' (Sum.elim aux b) := by
    have hred : zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW)
        (Sum.elim aux b) =
      Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux)
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) b) := by
      funext o
      cases o <;> rfl
    rw [← hred]
    exact rationalCharacterIndividualReduction_apply qW χ' hW _
  have hu := uniform_complexMean_surjective_hom
    (zmodPiReduction (I := D) (rationalCharacterIndividualModulus_dvd qW χ' hW))
    (zmodPiReduction_surjective (rationalCharacterIndividualModulus_dvd qW χ' hW))
    (fun b => phase (rationalCharacterIndividualReduction qW χ' hW
      (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
        test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b))
  simpa only [FiniteProbabilityWeights.uniform_complexMean, hphase,
    rationalCharacterIndividualModulus_reduce_test qW χ' hW] using hu

theorem rationalCharacterIndividualReduction_partial_star_uniform
    (aux : Aux → ZMod N) (test : (D → ZMod qW) → ℂ) :
    (𝔼 b : D → ZMod N, star (χ' (Sum.elim aux b)) * test (zmodPiReduction hW b)) =
      𝔼 b : D → ZMod (rationalCharacterIndividualModulus qW χ'),
        star (rationalCharacterIndividualReduction qW χ' hW
          (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
            test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b) :=
  rationalCharacterIndividualReduction_partial_phase_uniform qW hW χ' aux star test

end Partial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RetainedCharacterGridSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem retainedCharacterGrid_tsum {K Χ : Type*}
    (S : Finset Χ) (coeff : Χ → ℂ) (g : K → ℂ)
    (phase : Χ → K → ℂ) (φ : K → ℂ) (v : ℂ)
    (hs : ∀ χ ∈ S, Summable (fun k => phase χ k * g k * φ k)) :
    (∑' k, g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k) / v =
      ∑ χ ∈ S, coeff χ * ((∑' k, phase χ k * g k * φ k) / v) := by
  have he (k : K) : g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k =
      ∑ χ ∈ S, coeff χ * (phase χ k * g k * φ k) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun χ hχ => (hs χ hχ).mul_left (coeff χ))]
  simp_rw [tsum_mul_left, Finset.sum_div, mul_div_assoc]

theorem retainedCharacterGrid_expect {B Χ : Type*} [Fintype B]
    (S : Finset Χ) (coeff : Χ → ℂ) (phase : Χ → B → ℂ) (φ : B → ℂ) :
    (𝔼 b, (∑ χ ∈ S, coeff χ * phase χ b) * φ b) =
      ∑ χ ∈ S, coeff χ * (𝔼 b, phase χ b * φ b) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem retainedCharacterGrid_norm_sub_le {Χ : Type*}
    (S : Finset Χ) (coeff disc cont : Χ → ℂ) {M E : ℝ}
    (hE : 0 ≤ E) (hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤ M)
    (he : ∀ χ ∈ S, ‖disc χ - cont χ‖ ≤ E) :
    ‖(∑ χ ∈ S, coeff χ * disc χ) - (∑ χ ∈ S, coeff χ * cont χ)‖ ≤ M * E := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ χ ∈ S, ‖coeff χ * (disc χ - cont χ)‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ S, ‖coeff χ‖ * E := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he χ hχ) (norm_nonneg _)
    _ = (∑ χ ∈ S, ‖coeff χ‖) * E := (Finset.sum_mul ..).symm
    _ ≤ M * E := mul_le_mul_of_nonneg_right hcoeff hE

theorem retainedCharacterGrid_tsum_sub_expect_le {K B Χ : Type*} [Fintype B]
    (S : Finset Χ) (coeff : Χ → ℂ) (g : K → ℂ)
    (phase : Χ → K → ℂ) (φ : K → ℂ) (v : ℂ)
    (refPhase : Χ → B → ℂ) (refTest : B → ℂ) {M E : ℝ}
    (hs : ∀ χ ∈ S, Summable (fun k => phase χ k * g k * φ k))
    (hE : 0 ≤ E) (hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤ M)
    (he : ∀ χ ∈ S, ‖(∑' k, phase χ k * g k * φ k) / v -
      (𝔼 b, refPhase χ b * refTest b)‖ ≤ E) :
    ‖(∑' k, g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k) / v -
      (𝔼 b, (∑ χ ∈ S, coeff χ * refPhase χ b) * refTest b)‖ ≤ M * E := by
  rw [retainedCharacterGrid_tsum S coeff g phase φ v hs,
    retainedCharacterGrid_expect S coeff refPhase refTest]
  exact retainedCharacterGrid_norm_sub_le S coeff _ _ hE hcoeff he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerResidueLatticeSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} (q : ℕ) [NeZero q]

theorem tsum_integerResidueLatticePoint [Fintype J]
    (f : (J → ℤ) → ℂ) (hf : Summable f) :
    ∑' x, f x = ∑ r : J → ZMod q, ∑' k, f (integerResidueLatticePoint q r k) := by
  classical
  let e := integerResidueLatticeEquiv (J := J) q
  have he : Summable (fun p => f (e p)) := e.summable_iff.2 hf
  calc
    _ = ∑' p, f (e p) := (e.tsum_eq f).symm
    _ = ∑' r, ∑' k, f (integerResidueLatticePoint q r k) := he.tsum_prod
    _ = _ := tsum_fintype _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ComplexDensityScaledQuadrature
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

theorem density_complex_test_lipschitz {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (φ : X → ℂ) (C L K : ℝ≥0)
    (hg : LipschitzWith L g) (hφ : LipschitzWith K φ)
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (L + C * K) (fun x => (g x : ℂ) * φ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hg' : ‖(g x : ℂ) - g y‖ ≤ (L : ℝ) * dist x y := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, ← dist_eq_norm] using hg.dist_le_mul x y
  have hφ' : ‖φ x - φ y‖ ≤ (K : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hφ.dist_le_mul x y
  calc
    _ = ‖((g x : ℂ) - g y) * φ x + (g y : ℂ) * (φ x - φ y)‖ := by congr 1; ring
    _ ≤ ‖((g x : ℂ) - g y) * φ x‖ + ‖(g y : ℂ) * (φ x - φ y)‖ := norm_add_le _ _
    _ ≤ ((L : ℝ) * dist x y) * 1 + C * ((K : ℝ) * dist x y) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hg' (hbound x) (norm_nonneg _) (by positivity))
        (mul_le_mul (hcap y) hφ' (norm_nonneg _) C.coe_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

theorem translatedGridMass_error (g : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L g) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, 1 / T j ≤ δ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    |translatedGridMass g center T - ∫ x, g x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ :=
  rectangularLattice_quadrature g hLip center T hT hR hδ hδ1 hmesh hsupport

theorem translatedGridMass_le (g : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L g) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, 1 / T j ≤ δ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    translatedGridMass g center T ≤ (∫ x, g x) +
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have h := (le_abs_self _).trans (translatedGridMass_error g hLip center T hT
    hR hδ hδ1 hmesh hsupport)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_zero_off_image {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  rw [rationalInactiveForecast,
    inactive.fiberMean_eq_zero_of_not_mem_image gridPoint _ z hz, mul_zero]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

theorem periodicTranslatedIntegerGrid_summable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Summable (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rectangularWeightIndices center T R) ?_).summable
  intro k hk
  have h := rectangularWeight_zero_off_indices
    (fun x => ‖f (fun j => (k j : ZMod q)) x‖) center T hT
    (fun x hx => by rw [hsupport _ x hx, norm_zero]) k hk
  change ‖f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)‖ = 0 at h
  exact norm_eq_zero.mp h

theorem periodicTranslatedIntegerGrid_complex_quadrature (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : ∀ r, LipschitzWith L (f r)) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (q : ℝ) / T j ≤ δ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    ‖(∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) - 𝔼 r : J → ZMod q, ∫ x, f r x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  let disc := fun r : J → ZMod q =>
    (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
      ∑' k : J → ℤ, f r (fun j => ((r j).val - center j + (q : ℝ) * k j) / T j)
  let cont := fun r : J → ZMod q => ∫ x, f r x
  have havg := (FiniteProbabilityWeights.uniform (J → ZMod q)).norm_complexMean_sub_le
    disc cont (fun _ => 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)
    (fun r _ => scaledRectangular_complex_quadrature _ (hLip r) _ T
      (Nat.cast_pos.mpr (NeZero.pos q)) hT hR hδ hδ1 hmesh (hsupport r))
  rw [FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.mean_const] at havg
  have hsum := tsum_integerResidueLatticePoint q
    (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j))
    (periodicTranslatedIntegerGrid_summable q f center T hT hsupport)
  have hcast (r : J → ZMod q) (k : J → ℤ) :
      (fun j => (integerResidueLatticePoint q r k j : ZMod q)) = r := by
    funext j
    exact integerResidueLatticePoint_cast q r k j
  simp_rw [hcast] at hsum
  simp only [integerResidueLatticePoint, Int.cast_add, Int.cast_natCast, Int.cast_mul, add_sub_right_comm] at hsum
  have he : (𝔼 r : J → ZMod q, disc r) =
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) := by
    rw [hsum]
    simp only [Finset.expect_eq_sum_div_card, disc, ← Finset.mul_sum,
      Finset.card_univ, Fintype.card_fun, ZMod.card]
    push_cast
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  rw [he] at havg
  exact havg

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

private theorem constantPhase_density_test_lipschitz {X : Type*} [PseudoMetricSpace X]
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1)
    (g : X → ℝ) (φ : X → ℂ) (C L K : ℝ≥0)
    (hg : LipschitzWith L g) (hφ : LipschitzWith K φ)
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (L + C * K) (fun x => phase * (g x : ℂ) * φ x) := by
  have h := density_complex_test_lipschitz g φ C L K hg hφ hcap hbound
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (phase * (g x : ℂ) * φ x) (phase * (g y : ℂ) * φ y) =
        ‖phase‖ * dist ((g x : ℂ) * φ x) ((g y : ℂ) * φ y) := by
      simp only [dist_eq_norm, mul_assoc, ← mul_sub, norm_mul]
    _ ≤ 1 * dist ((g x : ℂ) * φ x) ((g y : ℂ) * φ y) :=
      mul_le_mul_of_nonneg_right hphase (dist_nonneg)
    _ ≤ _ := by simpa only [one_mul] using h.dist_le_mul x y

variable {Aux J : Type*} [Fintype Aux] [Fintype J]

theorem retainedRationalCharacter_grid_quadrature
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (aux : Aux → ZMod N)
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (rationalCharacterIndividualModulus qW χ : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' k : J → ℤ, star (χ (Sum.elim aux (fun j => (k j : ZMod N)))) *
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N, star (χ (Sum.elim aux b)) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ := by
  let q := rationalCharacterIndividualModulus qW χ
  let ψ := rationalCharacterIndividualReduction qW χ hW
  let auxq : Aux → ZMod q := zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) aux
  let f : (J → ZMod q) → (J → ℝ) → ℂ := fun b x =>
    star (ψ (Sum.elim auxq b)) * (g x : ℂ) *
      φ (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b) x
  have hLip : ∀ b, LipschitzWith (L + C * K) (f b) := by
    intro b
    exact constantPhase_density_test_lipschitz _
      (by simp only [norm_star, AddChar.norm_apply, le_refl])
      g _ C L K hg (hφ _) hcap (hbound _)
  have hsupp : ∀ b x, R < ‖x‖ → f b x = 0 := by
    intro b x hx
    simp only [f, hsupport x hx, Complex.ofReal_zero, mul_zero, zero_mul]
  have h := periodicTranslatedIntegerGrid_complex_quadrature q f hLip center T hT
    hR hδ hδ1 hmesh hsupp
  have heval (k : J → ℤ) :
      f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j) =
        star (χ (Sum.elim aux (fun j => (k j : ZMod N)))) *
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j) := by
    have hp := rationalCharacterIndividualReduction_apply qW χ hW
      (Sum.elim aux (fun j => (k j : ZMod N)))
    have he : zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)
        (Sum.elim aux (fun j => (k j : ZMod N))) =
        Sum.elim auxq (fun j => (k j : ZMod q)) := by
      funext j
      cases j <;> simp only [zmodPiReduction_apply, Sum.elim_inl, Sum.elim_inr,
        map_intCast, auxq]
    rw [he] at hp
    have htest : zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ)
        (fun j => (k j : ZMod q)) = (fun j => (k j : ZMod qW)) := by
      funext j
      exact map_intCast (ZMod.castHom (rationalCharacterIndividualModulus_test_dvd qW χ) (ZMod qW)) (k j)
    simp only [f, ψ, hp, htest]
  have havg : (𝔼 b : J → ZMod q, ∫ x, f b x) =
      𝔼 b : J → ZMod N, star (χ (Sum.elim aux b)) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x := by
    simp only [f, mul_assoc, integral_const_mul]
    exact (rationalCharacterIndividualReduction_partial_star_uniform qW hW χ aux
      (fun b => ∫ x, (g x : ℂ) * φ b x)).symm
  simpa only [heval, havg, NNReal.coe_add, NNReal.coe_mul] using h

theorem retainedRationalOutput_grid_quadrature
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (Y : Ω → (Aux ⊕ J) → ℤ)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ)
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    let S := Finset.univ.filter
      (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff)
    let coeff := fun χ => finiteImageCharacteristic p (fun ω o => (Y ω o : ZMod N)) χ
    ‖(∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (∑ χ ∈ S, coeff χ * star (χ (Sum.elim aux (fun j => (k j : ZMod N))))) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N,
        (∑ χ ∈ S, coeff χ * star (χ (Sum.elim aux b))) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) := by
  let S := Finset.univ.filter
    (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff)
  let coeff := fun χ => finiteImageCharacteristic p (fun ω o => (Y ω o : ZMod N)) χ
  let grid : (J → ℤ) → J → ℝ := fun k j => ((k j : ℝ) - center j) / T j
  let phase := fun (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (k : J → ℤ) =>
    star (χ (Sum.elim aux (fun j => (k j : ZMod N))))
  let test := fun k : J → ℤ => φ (fun j => (k j : ZMod qW)) (grid k)
  let refPhase := fun (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (b : J → ZMod N) =>
    star (χ (Sum.elim aux b))
  let refTest := fun b : J → ZMod N => ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  let err : ℝ := 2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ
  have hs (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) :
      Summable (fun k : J → ℤ => phase χ k * (g (grid k) : ℂ) * test k) := by
    have hsum := periodicTranslatedIntegerGrid_summable (R := R) N
      (fun b x => star (χ (Sum.elim aux b)) * (g x : ℂ) * φ (zmodPiReduction hW b) x)
      center T hT (fun b x hx => by
        simp only [hsupport x hx, Complex.ofReal_zero, mul_zero, zero_mul])
    have hr (k : J → ℤ) : zmodPiReduction hW (fun j => (k j : ZMod N)) =
        (fun j => (k j : ZMod qW)) := by
      funext j
      exact map_intCast (ZMod.castHom hW (ZMod qW)) (k j)
    simpa only [hr] using hsum
  have hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) :=
    finiteImage_boundedOrder_coefficient_mass
      (integerResidueTuple (J := Aux ⊕ J) N) (integerResidueTuple_surjective N)
      p (fun ω o => (Y ω o : ZMod N)) cutoff
  have he (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (hχ : χ ∈ S) :
      ‖(∑' k, phase χ k * (g (grid k) : ℂ) * test k) / ((∏ j, T j : ℝ) : ℂ) -
        (𝔼 b, refPhase χ b * refTest b)‖ ≤ err := by
    have hm (j) : (rationalCharacterIndividualModulus qW χ : ℝ) / T j ≤ δ := by
      have hq := rationalCharacterIndividualModulus_le_mul qW χ (Finset.mem_filter.mp hχ).2
      exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hq) (hT j).le).trans (hmesh j)
    exact retainedRationalCharacter_grid_quadrature qW hW χ aux g φ C L K hg hφ
      hcap hbound center T hT hR hδ hδ1 hm hsupport
  exact retainedCharacterGrid_tsum_sub_expect_le S coeff
    (fun k => (g (grid k) : ℂ)) phase test ((∏ j, T j : ℝ) : ℂ)
    refPhase refTest (fun χ _ => hs χ) (by positivity) hcoeff he

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J : Type*} [Fintype Ω] [Fintype Aux] [Fintype J]

theorem rationalOutput_translated_grid_comparison
    (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N,
        (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) := by
  classical
  let trunc := fun b : (Aux ⊕ J) → ZMod N =>
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff),
      finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)
  let raw := (∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
      φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ)
  let rawRet := (∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      trunc (Sum.elim aux (fun j => (k j : ZMod N))) *
      φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ)
  let refRet := 𝔼 b : J → ZMod N, trunc (Sum.elim aux b) *
    ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  let ref := 𝔼 b : J → ZMod N,
    (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
      ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  have hunit : ∀ j, 1 / T j ≤ δ := by
    intro j
    apply le_trans _ (hmesh j)
    apply div_le_div_of_nonneg_right _ (hT j).le
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (NeZero.pos qW) hcutoff)
  have hm := translatedGridMass_le g hg center T hT hR hδ hδ1 hunit hsupport
  have hd0 : 0 ≤ D / cutoff := div_nonneg hD (Nat.cast_nonneg _)
  have hraw0 := rationalOutputOrderTail_normalized_grid_le p Y N hD hP hdecay cutoff hcutoff
    g hg0 center T hT R hsupport (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun k => φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))
    (fun k => hbound _ _)
  rw [rationalOutputOrderTail_grid_difference p Y N cutoff g center T hT R hsupport
    (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun k => φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))] at hraw0
  have hraw : ‖raw - rawRet‖ ≤ (D / cutoff) * ((∫ x, g x) +
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) :=
    hraw0.trans (mul_le_mul_of_nonneg_left hm hd0)
  have href0 := rationalOutputOrderTail_mean_integral_le volume p Y N hD hP hdecay cutoff hcutoff
    g hg0 (compactBox_integrable g hg.continuous R hsupport) (fun b : J → ZMod N => Sum.elim aux b)
    (fun b x => φ (zmodPiReduction hW b) x) (fun b x => hbound _ _)
  have hdiff : (𝔼 b : J → ZMod N, rationalOutputOrderTail p Y N cutoff (Sum.elim aux b) *
      ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x) = ref - refRet := by
    simp only [rationalOutputOrderTail, sub_mul, Finset.expect_sub_distrib, ref, refRet, trunc]
  rw [hdiff, norm_sub_rev] at href0
  have hret := retainedRationalOutput_grid_quadrature p Y qW hW aux cutoff
    g φ C L K hg hφ hcap hbound center T hT hR hδ hδ1 hmesh hsupport
  change ‖raw - ref‖ ≤ _
  have ht := (norm_sub_le_norm_sub_add_norm_sub raw rawRet ref).trans
    (add_le_add hraw ((norm_sub_le_norm_sub_add_norm_sub rawRet refRet ref).trans
      (add_le_add hret href0)))
  exact ht.trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalInactivePartialReference
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I A Z O : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_pointwise_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : O → ZMod N) (test : Z → ℂ) :
    (∑' z, ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i)) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  exact (inactive.complexMean_fiber_factor_sum_image gridPoint
    (fun i => rationalOutputDensity (active i) (Y i) N b) test).symm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalInactiveForecast_partial_reference
    {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O] [Fintype K]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, 𝔼 k : K,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => 𝔼 k : K,
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  rw [← Finset.expect_sum_comm]
  have he (k : K) : (∑ z ∈ Finset.univ.image gridPoint,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
        test (gridPoint i) k) := by
    simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
    exact (inactive.complexMean_fiber_factor_sum_image gridPoint
      (fun i => rationalOutputDensity (active i) (Y i) N (b k)) (fun z => test z k)).symm
  simp_rw [he]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp only [Finset.mul_expect]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RationalInactiveLatticeContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_lattice_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => ∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) := by
  let grid := Finset.univ.image gridPoint
  have hz (z : Z) (hz : z ∉ grid) (k : K) :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) = 0 :=
    rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz (b k)
  rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h, zero_div,
    Complex.ofReal_zero, mul_zero, zero_mul, tsum_zero])]
  have hk (z : Z) : (∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      ∑ k ∈ sK, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hk]
  rw [Finset.sum_comm]
  have hzsum (k : K) :
      (∑ z ∈ grid, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k) =
      G k * inactive.complexMean (fun i =>
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
    rw [← rationalInactiveForecast_pointwise_tsum_test inactive active gridPoint Y N hV
      (b k) (fun z => test z k)]
    rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h k, zero_div,
      Complex.ofReal_zero, zero_mul])]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [hzsum]
  have hi (i : I) : (∑' k, G k *
      (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) =
      ∑ k ∈ sK, G k *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hi, FiniteProbabilityWeights.complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rationalInactiveForecast_lattice_tsum_test_div
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) (v : ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / v =
      inactive.complexMean (fun i => (∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / v) := by
  rw [rationalInactiveForecast_lattice_tsum_test inactive active gridPoint Y N hV G sK hG b test]
  simp only [FiniteProbabilityWeights.complexMean, Finset.sum_div, mul_div_assoc]

theorem rationalInactiveForecast_compactGrid_tsum_test_div {J : Type*} [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ)
    (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (test : Z → (J → ℤ) → ℂ) :
    (∑' z, ∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / ((∏ j, scale j : ℝ) : ℂ) =
      inactive.complexMean (fun i => (∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / ((∏ j, scale j : ℝ) : ℂ)) := by
  apply rationalInactiveForecast_lattice_tsum_test_div inactive active gridPoint Y N hV
    _ (rectangularWeightIndices center scale R) _ b test
  intro k hk
  have h := rectangularWeight_zero_off_indices g center scale hscale hsupport k hk
  unfold rectangularWeight rectangularLatticePoint at h
  rw [h, Complex.ofReal_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalInactiveGridIntegralComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J]

theorem rationalInactive_translated_grid_comparison_s2_oai
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : (J → ℝ) → ℝ) (φ : Z → (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' z, ∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x, (g x : ℂ) * φ z (zmodPiReduction hW b) x)‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) := by
  classical
  rw [rationalInactiveForecast_compactGrid_tsum_test_div inactive active gridPoint Y N hV
    g center T hT R hsupport (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun z k => φ z (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))]
  rw [rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x, (g x : ℂ) * φ z (zmodPiReduction hW b) x)]
  apply (inactive.norm_complexMean_sub_le _ _
    (fun _ => (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
      (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) ?_).trans_eq (inactive.mean_const _)
  intro i _
  exact rationalOutput_translated_grid_comparison (active i) (Y i) qW hW aux cutoff hcutoff
    hD hP (hdecay i) g (φ (gridPoint i)) C L K hg hg0 (hφ _) hcap (hbound _)
    center T hT hR hδ hδ1 hmesh hsupport

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.rationalInactive_translated_grid_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.rationalInactive_translated_grid_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5}
