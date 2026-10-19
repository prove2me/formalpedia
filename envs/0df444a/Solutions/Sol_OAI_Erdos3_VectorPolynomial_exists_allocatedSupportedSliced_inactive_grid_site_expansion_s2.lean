-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:45:57.168987+00:00
-- url     : https://prove2.me/submissions/d43563a9-3fc8-42dd-a362-8e4822a71f32

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactivePointApproximation_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
import Theorems.Thm_OAI_Erdos3_exists_affineCube_plateau_site_approximation_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) (x : J → ℝ)
    (hx : ∀ j, |x j| ≤ H) : normalizedSupportPlateau H x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg hH).mpr (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizedSupportPlateau_support {H : ℝ} (x : J → ℝ)
    (hx : normalizedSupportPlateau H x ≠ 0) : ∀ j, |x j| < H + 1 / 4 := by
  have hn : ‖x‖ < H + 1 / 4 := by
    apply lt_of_not_ge
    intro h
    apply hx
    exact linearCutoff_eq_zero H (1 / 4) (by simpa using h)
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  exact hj.trans_lt hn

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem scalarSupportPlateau_norm (H x : ℝ) : ‖scalarSupportPlateau H x‖ ≤ 1 := by
  rw [scalarSupportPlateau, Complex.norm_real,
    Real.norm_of_nonneg (normalizedSupportPlateau_range H _).1]
  exact (normalizedSupportPlateau_range H _).2

theorem scalarSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    scalarSupportPlateau H x = 1 := by
  simp only [scalarSupportPlateau, normalizedSupportPlateau_one hH _ (fun _ => hx), Complex.ofReal_one]

theorem scalarSupportPlateau_support (H x : ℝ) (hx : scalarSupportPlateau H x ≠ 0) :
    |x| < H + 1 / 4 := by
  apply normalizedSupportPlateau_support (fun _ : Unit => x) _ ()
  intro hz
  exact hx (by simp only [scalarSupportPlateau, hz, Complex.ofReal_zero])

theorem scalarSupportPlateau_zero {H x : ℝ} (hx : H + 1 / 4 ≤ |x|) :
    scalarSupportPlateau H x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (scalarSupportPlateau_support H x hn)

theorem scalarSupportPlateau_lipschitz (H : ℝ) : LipschitzWith 4 (scalarSupportPlateau H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (normalizedSupportPlateau_lipschitz (J := Unit) H).dist_le_mul
    (fun _ => x) (fun _ => y)
  rw [dist_pi_const] at h
  simpa only [scalarSupportPlateau, dist_eq_norm,
    ← Complex.ofReal_sub, Complex.norm_real] using h

theorem scalarSupportPlateau_mul_lipschitz (H : ℝ) (f : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) (hf : ∀ x, ‖f x‖ ≤ 1) :
    LipschitzWith (L + 4) (fun x => scalarSupportPlateau H x * f x) := by
  simpa only [one_mul] using lipschitz_mul_of_bounds (scalarSupportPlateau H) f
    (scalarSupportPlateau_lipschitz H) hL (Bf := 1) (Bg := 1)
    (scalarSupportPlateau_norm H) hf

theorem finite_site_cutoff_error {T S : Type*} [Fintype T] [Fintype S]
    (target : ℂ) (c : T → ℂ) (f : T → S → ℂ) (χ : S → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (hkeep : target ≠ 0 → ∀ s, χ s = 1)
    (he : (∀ s, χ s ≠ 0) → ‖target - ∑ k, c k * ∏ s, f k s‖ ≤ ε) :
    ‖target - ∑ k, c k * ∏ s, χ s * f k s‖ ≤ ε := by
  have hid : (∑ k, c k * ∏ s, χ s * f k s) =
      (∏ s, χ s) * ∑ k, c k * ∏ s, f k s := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ht : (∏ s, χ s) * target = target := by
    by_cases hz : target = 0
    · simp only [hz, mul_zero]
    · simp only [hkeep hz, Finset.prod_const_one, one_mul]
  rw [hid, ← ht, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hp : ‖∏ s, χ s‖ ≤ 1 := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hχ s)).trans_eq
        (Finset.prod_const_one)
    exact (mul_le_mul hp (he (fun s hs => hz ⟨s, hs⟩)) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PMFPointMassMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_toReal_hasSum {X : Type*} (p : PMF X) :
    HasSum (fun x => (p x).toReal) 1 := by
  have hs : Summable (fun x => (p x).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have ht : (∑' x, (p x).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe, ENNReal.toReal_one]
  simpa only [ht] using hs.hasSum

theorem pmf_complex_average_summable {X : Type*} (p : PMF X)
    (f : X → ℂ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    Summable (fun x => ((p x).toReal : ℂ) * f x) := by
  apply ((pmf_toReal_hasSum p).summable.mul_right B).of_norm_bounded
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg

theorem pmf_complex_average_error {X : Type*} (p : PMF X)
    (f g : X → ℂ) {Bf Bg ε : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (he : ∀ x, ‖f x - g x‖ ≤ ε) :
    ‖(∑' x, ((p x).toReal : ℂ) * f x) -
      ∑' x, ((p x).toReal : ℂ) * g x‖ ≤ ε := by
  rw [← (pmf_complex_average_summable p f hf).tsum_sub
    (pmf_complex_average_summable p g hg)]
  have hw : HasSum (fun x => (p x).toReal * ε) ε := by
    simpa only [one_mul] using (pmf_toReal_hasSum p).mul_right ε
  apply tsum_of_norm_bounded hw
  intro x
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (he x) ENNReal.toReal_nonneg

theorem pmf_bind_scaled_complex_average {X Y : Type*}
    (p : PMF X) (q : X → PMF Y) (C : ℝ) (y : Y) :
    (∑' x, ((p x).toReal : ℂ) * ((C * (q x y).toReal : ℝ) : ℂ)) =
      ((C * ((p.bind q) y).toReal : ℝ) : ℂ) := by
  simp only [pmf_bind_toReal, Complex.ofReal_mul, Complex.ofReal_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  ring

theorem pmf_bind_point_error {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    (a : X → ℂ) {C ε : ℝ} (hC : 0 ≤ C) (y : Y)
    (he : ∀ x, ‖((C * (q x y).toReal : ℝ) : ℂ) - a x‖ ≤ ε) :
    ‖((C * ((p.bind q) y).toReal : ℝ) : ℂ) -
      ∑' x, ((p x).toReal : ℂ) * a x‖ ≤ ε := by
  let f (x : X) : ℂ := ((C * (q x y).toReal : ℝ) : ℂ)
  have hf (x : X) : ‖f x‖ ≤ C := by
    have hp : (q x y).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((q x).coe_le_one y)
    change ‖((C * (q x y).toReal : ℝ) : ℂ)‖ ≤ C
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC ENNReal.toReal_nonneg)]
    exact (mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_one C)
  have ha (x : X) : ‖a x‖ ≤ C + ε := by
    calc
      ‖a x‖ = ‖(a x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖a x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ ε + C := add_le_add (by simpa only [norm_sub_rev] using he x) (hf x)
      _ = C + ε := add_comm _ _
  have h := pmf_complex_average_error p f a hf ha he
  change ‖(∑' x, ((p x).toReal : ℂ) * ((C * (q x y).toReal : ℝ) : ℂ)) -
    ∑' x, ((p x).toReal : ℂ) * a x‖ ≤ ε at h
  rw [pmf_bind_scaled_complex_average] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]

theorem pmf_bind_point_approximation_error (p : PMF X) (q : X → PMF Y)
    (z : Y) (approx : X → ℂ) {K ε : ℝ} (hK : 0 ≤ K)
    (herr : ∀ x, ‖((K * (q x z).toReal : ℝ) : ℂ) - approx x‖ ≤ ε) :
    ‖((K * ((p.bind q) z).toReal : ℝ) : ℂ) - ∫ x, approx x ∂p.toMeasure‖ ≤ ε := by
  let f (x : X) : ℂ := (K * (q x z).toReal : ℝ)
  have hf (x : X) : ‖f x‖ ≤ K := by
    have hb : (q x z).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((q x).coe_le_one z)
    change ‖((K * (q x z).toReal : ℝ) : ℂ)‖ ≤ K
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hK ENNReal.toReal_nonneg)]
    exact mul_le_of_le_one_right hK hb
  have ha (x : X) : ‖approx x‖ ≤ ε + K := by
    calc
      _ = ‖(approx x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖approx x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ ε + K := add_le_add (by simpa only [norm_sub_rev] using herr x) (hf x)
  have hai : Integrable approx p.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (ε + K) (ae_of_all _ ha)
  rw [p.integral_eq_tsum approx hai]
  simpa only [Complex.real_smul] using pmf_bind_point_error p q approx hK z herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

theorem unscale_grid_interval {M H d : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ)
    (h : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) / M - (a : ℝ) / d =
      ((k.val : ℝ) - M * ((a : ℝ) / d)) / M := by field_simp
  rw [he, abs_div, abs_of_pos hM']
  exact div_le_div_of_nonneg_right h hM'.le

theorem rationalGridMajorSet_rational {M Q H : ℕ} (hM : 0 < M) (k : Fin M)
    (hk : k ∈ rationalGridMajorSet M Q H) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ (Q + 1 : ℝ) ∧
      ∃ a : ℤ, |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  classical
  obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
  have he := (Finset.mem_filter.mp hk).2
  by_cases hd0 : d = 0
  · refine ⟨1, by omega, by exact_mod_cast (show 1 ≤ Q + 1 by omega), 0, ?_⟩
    apply unscale_grid_interval hM k 0
    simpa only [hd0, Nat.cast_zero, div_zero, Int.cast_zero, zero_div, mul_zero, sub_zero] using he
  · refine ⟨d, Nat.pos_of_ne_zero hd0, ?_, a, unscale_grid_interval hM k a he⟩
    exact_mod_cast (Finset.mem_range.mp hd).le

theorem rationalGridMajorBox_character {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  have hj := Fintype.mem_piFinset.mp hk
  obtain ⟨D, hD, hDQ, a, ha⟩ := exists_common_rational_approximations
    (fun j => ((k j).val : ℝ) / M) (fun j => rationalGridMajorSet_rational hM (k j) (hj j))
  let ξ j := (M : ℝ) * (((k j).val : ℝ) / M - (a j : ℝ) / D)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨D, hD, hDQ, a, ξ, ?_, ?_⟩
  · intro j
    dsimp only [ξ]
    rw [abs_mul, abs_of_pos hM']
    calc
      _ ≤ (M : ℝ) * ((H : ℝ) / M) := mul_le_mul_of_nonneg_left (ha j) hM'.le
      _ = H := by field_simp
  · intro j
    dsimp only [ξ]
    field_simp
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rationalGridMajorBox_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M Q H : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hM0 : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  obtain ⟨D, hD, hDQ, a, ξ, hξ, he⟩ := rationalGridMajorBox_character hM k hk
  refine ⟨D, hD, hDQ, a, (fun j => (K : ℝ) * ξ j / M), ?_, ?_⟩
  · intro j
    simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
      abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
    calc
      (K : ℝ) * |ξ j| ≤ (K : ℝ) * H := mul_le_mul_of_nonneg_left (hξ j) (Nat.cast_nonneg K)
      _ ≤ (M : ℝ) * H := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKM) (Nat.cast_nonneg H)
      _ = (H : ℝ) * M := mul_comm _ _
  · intro j
    rw [he j]
    congr 1
    field_simp

theorem lengthAwarePolynomialGrid_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    {C L V A ζ : ℝ} {c t r : ℕ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ V * L ^ t)
    (k : J → Fin M)
    (hk : k ∈ lengthAwareSpectrumCover C L c (polynomialGridCover J M A r) ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ max ((⌈A / ζ ^ r⌉₊ + 1 : ℝ) ^ Fintype.card J)
        (V * C ^ t / ζ ^ (c * t)) ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ (⌈A / ζ ^ r⌉₊ : ℝ)) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · have hk' : k ∈ rationalGridMajorBox J M ⌈A / ζ ^ r⌉₊ ⌈A / ζ ^ r⌉₊ := by
      simpa only [lengthAwareSpectrumCover, if_pos hstart, polynomialGridCover] using hk
    obtain ⟨D, hD, hb, a, ω, hω, he⟩ := rationalGridMajorBox_scaled_character hK hKM k hk'
    exact ⟨D, hD, hb.trans (le_max_left _ _), a, ω, hω, he⟩
  · cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨1, Nat.zero_lt_one, ?_, (fun j => isEmptyElim j),
        (fun j => isEmptyElim j), (fun j => isEmptyElim j), (fun j => isEmptyElim j)⟩
      simpa only [Fintype.card_eq_zero, pow_zero, Nat.cast_one] using
        (le_max_left (1 : ℝ) (V * C ^ t / ζ ^ (c * t)))
    | inr hJ =>
      let := hJ
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hpow : (M : ℝ) ≤ (M : ℝ) ^ Fintype.card J :=
        le_self_pow₀ (by exact_mod_cast hM) (Fintype.card_pos.ne')
      have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
      refine ⟨M, hM, (hpow.trans hb).trans (le_max_right _ _),
        (fun j => ((k j).val : ℤ)), (fun _ => 0), ?_, ?_⟩
      · intro j
        simpa only [abs_zero] using (Nat.cast_nonneg ⌈A / ζ ^ r⌉₊ : (0 : ℝ) ≤ _)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]

end Erdos3

end

section

namespace Erdos3

theorem uniformBlockSpectrumCover_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ω : J → ℝ),
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K :=
  lengthAwarePolynomialGrid_character hK hKM hL hW hsize k hk

theorem uniformBlockSpectrumCover_modes {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ∃ (D : (J → Fin M) → ℕ) (a : (J → Fin M) → J → ℤ) (ω : (J → Fin M) → J → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ uniformBlockSpectrumCover J M n U V L ζ,
        (D k : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω k j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a k j : ℝ) / D k + ω k j / K := by
  classical
  have hex (k : J → Fin M) : ∃ D : ℕ, 0 < D ∧ ∃ (a : J → ℤ) (ω : J → ℝ),
      k ∈ uniformBlockSpectrumCover J M n U V L ζ →
        (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
    by_cases hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ
    · obtain ⟨D, hD, hb, a, ω, hω, he⟩ :=
        uniformBlockSpectrumCover_scaled_character hK hKM n t hL hW hsize k hk
      exact ⟨D, hD, a, ω, fun _ => ⟨hb, hω, he⟩⟩
    · exact ⟨1, Nat.zero_lt_one, 0, 0, fun h => (hk h).elim⟩
  choose D hD a ω h using hex
  exact ⟨D, a, ω, hD, h⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

theorem grid_scale_factor_le_one (R K j : ℕ) (hR : 0 < R) (hK : 0 < K) :
    ((K : ℝ) / (R * K)) ^ j ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  apply pow_le_one₀ (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedCubePlateau
namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance blockTorusFactor_neZero (q h b : ℕ) (A : ℝ) : NeZero (blockTorusFactor q h b A) :=
  ⟨(blockTorusFactor_pos q h b A).ne'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integer_boolean_reconstruction (y : Finset α → ℤ) (s : Finset α) :
    y s = ∑ t : Finset α, if t ⊆ s then booleanCoefficient y t else 0 := by
  have h := congrArg (fun M : Matrix (Finset α) (Finset α) ℤ => M *ᵥ y)
    (booleanReconstruction_mul_extraction (α := α))
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  have hv : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := by
    funext t
    exact booleanJetExtractionMatrix_mulVec id y t
  rw [hv] at h
  have hs := congrFun h s
  simpa only [Matrix.mulVec, dotProduct, booleanReconstructionMatrix,
    ite_mul, one_mul, zero_mul] using hs.symm

theorem integer_boolean_reconstruction_rows (y : Finset α → ℤ)
    (rows : Finset (Finset α)) (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (s : Finset α) :
    y s = ∑ t ∈ rows, if t ⊆ s then booleanCoefficient y t else 0 := by
  rw [integer_boolean_reconstruction y s]
  symm
  apply Finset.sum_subset (Finset.subset_univ rows)
  intro t _ ht
  simp only [hrows t ht, ite_self]

theorem integer_boolean_sites_bound (y : Finset α → ℤ) (rows : Finset (Finset α))
    (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    {H N : ℝ} (hH : 0 ≤ H) (hN : 0 < N)
    (hcoeff : ∀ t ∈ rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ H * N) (s : Finset α) :
    |(y s : ℝ) / N| ≤ rows.card * H := by
  have hs : |(y s : ℝ)| ≤ (rows.card : ℝ) * (H * N) := by
    rw [integer_boolean_reconstruction_rows y rows hrows s, Int.cast_sum]
    calc
      _ ≤ ∑ t ∈ rows, |((if t ⊆ s then booleanCoefficient y t else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ rows, H * N := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact hcoeff t ht
        · simp only [Int.cast_zero, abs_zero]
          positivity
      _ = _ := by simp
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_assoc] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite
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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

theorem allocatedSupportedSlicedInactivePhysicalGridApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ) -
        allocatedSupportedSlicedInactivePhysicalGridApproximation B U basis hR hσ S q hq r H step c hH j i hsize
          M rows F z‖ ≤ ε := by
  intro V t W ζ F
  obtain ⟨hF, hcap, he⟩ := allocatedSupportedSlicedInactivePointApproximation_error_s2 B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  refine ⟨hF, hcap, fun x z => ?_⟩
  unfold allocatedSupportedSlicedPhysicalGridPMF allocatedSupportedSlicedInactivePhysicalGridApproximation
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U basis hR hσ S q r H step c
    hH hsubset hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro zeta
  exact he (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in
theorem exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2_oai
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val rows.card t P V W
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((uniformSpectrumSizeConstant j.val rows.card t P V W /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (uniformScaledRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  intro V t W ζ freq cap R0 η Q hη hQ hRQ hηQ hLQ
  let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ ((torus : ℝ) * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg torus))
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hKM : height ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨D, a, ω, hD, hmodes⟩ := uniformBlockSpectrumCover_modes (J := rows)
    (basisAxisScale_pos (basis j) i) hKM j.val t hL hW
    (by simpa only [Fintype.card_coe] using hcard) (U := P) (V := V) (ζ := ζ)
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  obtain ⟨hF, hcap, hpoint⟩ := allocatedSupportedSlicedInactivePhysicalGridApproximation_error
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  have hRj : 0 ≤ R j := (hR j).le
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  obtain ⟨N, hN, hcount, β, f, hβ, hf, hLf, he⟩ := exists_affineCube_plateau_site_approximation_s2
    sources lower strides constantLaw (basisAxisScale_pos (basis j) i) radius rows F D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun zeta t => booleanCoefficient (fun _ : Finset α => zeta) t) hscale
    hcap freq
    (fun k hk t => (by simpa only [Fintype.card_coe] using (hmodes k hk).2.1 t :
      |ω k t| ≤ uniformScaledRetainedFrequencyBound j.val rows.card P V ζ).trans (Real.le_coe_toNNReal _))
    (R := R0 + 1 / 4) (by positivity) hη hQ hRQ hηQ hLQ
  let g (k : PlateauSiteIndex α F N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau R0 z * f k u v z
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := g }
  refine ⟨e, ⟨?_, (fun k => hD k.1), ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hcount.trans (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
  · intro k
    simpa only [Fintype.card_coe] using (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau R0 z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz R0 (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau R0 z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    have hkeep :
        (((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) ≠ 0 →
        ∀ u, scalarSupportPlateau R0 ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      apply scalarSupportPlateau_one hR0
      apply integer_boolean_sites_bound y rows hy (by positivity) (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      intro t ht
      have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2 B U basis hR hσ S q r H step c hH hsubset hcell
        j i hσ1 rows x (fun t => booleanCoefficient y t) hmass ⟨t, ht⟩
      have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
      rw [abs_div, abs_of_pos hk] at hb
      exact (div_le_iff₀ hk).mp hb
    exact finite_site_cutoff_error _ β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau R0 ((y u : ℝ) / height))
      (by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
      (fun hcut => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (hpoint x (fun t => booleanCoefficient y t))
          (he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le))))

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4}
