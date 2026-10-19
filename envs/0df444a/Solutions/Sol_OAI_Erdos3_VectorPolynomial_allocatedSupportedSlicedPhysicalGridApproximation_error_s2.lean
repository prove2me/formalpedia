-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridApproximation_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:43:10.176347+00:00
-- url     : https://prove2.me/submissions/60f1582f-d97e-4e30-bf20-e7bd5cccb89e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedGridDensity_approximation_on_cover_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

theorem integerGridResidue_eq_iff_of_close {J : Type*} (M : ℕ) (y z : J → ℤ)
    (hclose : ∀ j, |y j - z j| < (M : ℤ)) :
    integerGridResidue M y = integerGridResidue M z ↔ y = z := by
  constructor
  · intro h
    funext j
    have hd : (M : ℤ) ∣ y j - z j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Int.cast_sub, show (y j : ZMod M) = (z j : ZMod M) from congrFun h j, sub_self]
    have ha : (y j - z j).natAbs < (M : ℤ).natAbs := by
      have hj := hclose j
      rw [Int.abs_eq_natAbs] at hj
      exact_mod_cast hj
    exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ha)
  · rintro rfl
    rfl

theorem integerGridMass_eq_imageMass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ)
    (hclose : ∀ x, p.weight x ≠ 0 → ∀ j, |Y x j - z j| < (M : ℤ)) :
    integerGridMass p Y M z = finiteImageMass p Y z := by
  classical
  unfold integerGridMass finiteImageMass FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul]
  · simp only [integerGridResidue_eq_iff_of_close M (Y x) z (hclose x hx)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBooleanBlockValue_bound {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (L : G → ℕ) (hx : ∀ g r, |x g r| ≤ (L g : ℤ)) (t : Finset I) :
    |integerBooleanBlockValue x t| ≤ ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
  classical
  unfold integerBooleanBlockValue
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro g _
  calc
    _ ≤ ∑ r : Option I, |(booleanFeature r t : ℤ) * x g r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Option I, (L g : ℤ) := by
      apply Finset.sum_le_sum
      intro r _
      cases r with
      | none => simpa only [booleanFeature, one_mul] using hx g none
      | some i =>
          by_cases hi : i ∈ t
          · simpa only [booleanFeature, hi, ite_true, one_mul] using hx g (some i)
          · simp only [booleanFeature, hi, ite_false, zero_mul, abs_zero]
            exact Nat.cast_nonneg _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul]

theorem integerBooleanBlockJet_bound {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (L : G → ℕ) (hx : ∀ g r, |x g r| ≤ (L g : ℤ)) (S : Finset I) :
    |integerBooleanBlockJet x S| ≤ (2 : ℤ) ^ S.card *
      ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
  classical
  unfold integerBooleanBlockJet booleanCoefficient
  calc
    _ ≤ ∑ t ∈ S.powerset, |(-1 : ℤ) ^ (S \ t).card * integerBooleanBlockValue x t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ S.powerset, ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        integerBooleanBlockValue_bound x L hx t
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem integerScalarCubeBox_coordinate_abs {I : Type*} {L : ℕ}
    (x : IntegerScalarCubeBox I L) (r : Option I) : |(x r : ℤ)| ≤ L := by
  have h := Finset.mem_Ico.mp (x r).property
  rw [abs_le]
  constructor <;> omega

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

theorem normalizedSupportPlateau_grid_one {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 0 < K)
    (center z : J → ℤ) (hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K) :
    normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) = 1 := by
  apply normalizedSupportPlateau_one hH
  intro j
  rw [abs_div, abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
  exact (div_le_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mpr (hz j)

theorem normalizedSupportPlateau_grid_support {H : ℝ} {K : ℕ} (hK : 0 < K)
    (center z : J → ℤ)
    (hz : normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) ≠ 0) :
    ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K := by
  have h := normalizedSupportPlateau_support _ hz
  intro j
  have hj := h j
  rw [abs_div, abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)] at hj
  exact ((div_lt_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hj).le

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedModeratePointMass
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerGridPlateauTransfer
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_margin (H : ℝ) :
    2 * H + 1 ≤ (integerSupportTorusFactor H : ℝ) := by
  have h := Nat.le_ceil H
  simp only [integerSupportTorusFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem scaled_integer_support_close_buffered {J : Type*} (y z center : J → ℤ)
    {H : ℝ} {K : ℕ} (hK : 0 < K)
    (hy : ∀ j, |(y j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K) :
    ∀ j, |y j - z j| < (integerSupportTorusFactor H * K : ℕ) := by
  intro j
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hgap : (2 * H + 1 / 4) * K < (integerSupportTorusFactor H : ℝ) * K := by
    apply mul_lt_mul_of_pos_right _ hK'
    linarith [integerSupportTorusFactor_margin H]
  have ht : |(y j : ℝ) - z j| ≤ (2 * H + 1 / 4) * K := by
    calc
      _ = |((y j : ℝ) - center j) + (center j - z j)| := by congr 1; ring
      _ ≤ |(y j : ℝ) - center j| + |(center j : ℝ) - z j| := abs_add_le _ _
      _ ≤ H * K + (H + 1 / 4) * K :=
        add_le_add (hy j) (by simpa only [abs_sub_comm] using hz j)
      _ = _ := by ring
  have hlt := ht.trans_lt hgap
  exact_mod_cast hlt

theorem integerGridMass_eq_imageMass_on_buffered_support {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {H : ℝ} {K : ℕ} (hK : 0 < K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K) :
    integerGridMass p Y (integerSupportTorusFactor H * K) z = finiteImageMass p Y z := by
  apply integerGridMass_eq_imageMass
  intro x hx
  exact scaled_integer_support_close_buffered (Y x) z center hK (hY x hx) hz

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem integerGridDensity_plateau_transfer {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {H ε : ℝ} {K M : ℕ} (hH : 0 ≤ H) (hK : 0 < K)
    (hM : M = integerSupportTorusFactor H * K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (a : ℂ) (hε : 0 ≤ ε)
    (ha : ‖(integerGridDensity p Y K M z : ℂ) - a‖ ≤ ε) :
    ‖(((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ) : ℂ) -
      (normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) : ℂ) * a‖ ≤ ε := by
  let χ := normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K)
  let v : ℂ := ((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ)
  have hχ := normalizedSupportPlateau_range H (fun j => ((z j : ℝ) - center j) / K)
  have hfix : (χ : ℂ) * v = v := by
    by_cases hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K
    · have he : χ = 1 := normalizedSupportPlateau_grid_one hH hK center z hz
      simp only [he, Complex.ofReal_one, one_mul]
    · have he : finiteImageMass p Y z = 0 := by
        unfold finiteImageMass FiniteProbabilityWeights.mean
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : p.weight x = 0
        · simp only [hx, zero_mul]
        · have hn : Y x ≠ z := fun he => hz (he ▸ hY x hx)
          simp only [if_neg hn, mul_zero]
      rw [finiteImageMass_eq_toPMF] at he
      simp only [v, he, mul_zero, Complex.ofReal_zero]
  change ‖v - (χ : ℂ) * a‖ ≤ ε
  by_cases hχ0 : χ = 0
  · have hv : v = 0 := by simpa only [hχ0, Complex.ofReal_zero, zero_mul] using hfix.symm
    simpa only [hv, hχ0, Complex.ofReal_zero, zero_mul, sub_self, norm_zero] using hε
  · have hz := normalizedSupportPlateau_grid_support hK center z hχ0
    have hd : integerGridDensity p Y K M z =
        (K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal := by
      unfold integerGridDensity
      rw [hM, integerGridMass_eq_imageMass_on_buffered_support p Y center z hK hY hz,
        finiteImageMass_eq_toPMF]
    rw [hd] at ha
    calc
      _ = ‖(χ : ℂ) * (v - a)‖ := by rw [mul_sub, hfix]
      _ = χ * ‖v - a‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
      _ ≤ 1 * ε := mul_le_mul hχ.2 ha (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalIntervalLength_mul_scale_bounds {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    2 * γ * K ≤ (principalIntervalLength K T γ : ℝ) * T ∧
      (principalIntervalLength K T γ : ℝ) * T ≤ 4 * γ * K := by
  have hb := principalIntervalLength_bounds hK hT hγ hlarge
  constructor
  · calc
      2 * γ * K = (2 * γ * (K / T)) * T := by field_simp
      _ ≤ (principalIntervalLength K T γ : ℝ) * T := mul_le_mul_of_nonneg_right hb.1 hT.le
  · calc
      (principalIntervalLength K T γ : ℝ) * T ≤ (4 * γ * (K / T)) * T :=
        mul_le_mul_of_nonneg_right hb.2 hT.le
      _ = 4 * γ * K := by field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalNormalizedSource_scale_bounds :
    2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
        ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ∧
      ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ≤
        4 * gamma * (basisAxisScale (basis j) i : ℝ) := by
  change 2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
      (principalIntervalLength (basisAxisScale (basis j) i) ((S.value : ℝ) ^ (j.val + 1)) gamma : ℝ) *
        (S.value : ℝ) ^ (j.val + 1) ∧ _
  exact principalIntervalLength_mul_scale_bounds
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem NormalizedScalarCubeSource.source_cube {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (x : IntegerScalarCubeBox I s.length)
    (hx : s.source.weight x ≠ 0) : IntegerScalarCube s.length (fun i => (x i : ℤ)) := by
  have hb : s.baseLaw.weight x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hp := lt_of_le_of_ne (s.baseLaw.nonneg x) hb.symm
  rw [NormalizedScalarCubeSource.baseLaw, scalarCubeResidueWeights,
    FiniteProbabilityWeights.condition_weight_pos_iff] at hp
  have h1 := hp.2
  rw [integerScalarCubeWeights, FiniteProbabilityWeights.condition_weight_pos_iff] at h1
  exact (mem_integerScalarCubeSet s.length x).mp h1.1

theorem containedProgressionCoordinate_bound {I : Type*} [Fintype I] [DecidableEq I]
    {L H step : ℕ} (c : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (x : IntegerScalarCubeBox I H) (hx : IntegerScalarCube H (fun i => (x i : ℤ))) (i : Option I) :
    |(if i = none then c else 0) + (step : ℤ) * (x i : ℤ)| ≤ L := by
  have hb := integerScalarCube_coordinates (integerScalarCube_progression c hsubset _ hx) i
  exact abs_le.mpr ⟨hb.1.le, hb.2.le⟩

theorem weightedAffineModerateIntegerJetSum_box_bound
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (T : ℕ) (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, ((c b).length : ℝ) * (T : ℝ) ^ n ≤ A * K)
    (shift : rows → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length))
    (hcoord : ∀ b j i,
      |affineIntegerCubeCoordinates (u b j) (v b j) (fun i => ((x b).2 j i : ℤ)) i| ≤ T)
    (t : rows) :
    |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K := by
  have hb (b : B) : |weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) rows 0 (x b) t| ≤
      ((c b).length : ℤ) * ((2 : ℤ) ^ t.val.card *
        ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℤ) * T) := by
    unfold weightedAffineModerateIntegerBlock
    rw [zero_add, abs_mul]
    exact mul_le_mul (integerScalarCubeBox_coordinate_abs (x b).1 none)
      (integerBooleanBlockJet_bound _ (fun _ => T) (fun j i => hcoord b j i) t)
      (abs_nonneg _) (Nat.cast_nonneg _)
  have hs : |weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t - shift t| ≤
      ∑ b, ((c b).length : ℤ) * ((2 : ℤ) ^ t.val.card *
        ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℤ) * T) := by
    simp only [weightedAffineModerateIntegerJetSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => hb b))
  have hs' : |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      ∑ b, ((c b).length : ℝ) * ((2 : ℝ) ^ t.val.card *
        (((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (T : ℝ) ^ n)) := by
    have hh : |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
        ∑ b, ((c b).length : ℝ) * ((2 : ℝ) ^ t.val.card *
          ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℝ) * T) := by
      exact_mod_cast hs
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
  apply hs'.trans
  calc
    _ = ∑ b, (2 : ℝ) ^ t.val.card * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n *
        (((c b).length : ℝ) * (T : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ _b : B, (2 : ℝ) ^ n * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      apply (mul_le_mul_of_nonneg_left (hvol b) (by positivity)).trans
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hrows t t.property)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (by positivity)) (mul_nonneg hA hK)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedPoint
namespace OAI

section

namespace Erdos3.VectorPolynomial

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

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

omit [∀ layer, DecidableEq (I layer)] in
include hsubset in
theorem allocatedSupportedSlicedSource_support
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (shift : rows → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (coeff b).length ×
      (∀ v, IntegerScalarCubeBox α ((sources) b v).length))
    (hx : (weightedModerateIntegerProductSource coeff sources).weight x ≠ 0) (t : rows) :
    |(weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      radius * height := by
  have hcoord (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) :
      |affineIntegerCubeCoordinates (lower b v) (strides b v) (fun a => ((x b).2 v a : ℤ)) a| ≤ S.value := by
    have hb : (weightedModerateIntegerSource (coeff b) (sources b)).weight (x b) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
    have hprod : (∏ v, ((sources) b v).source.weight ((x b).2 v)) ≠ 0 :=
      (mul_ne_zero_iff.mp hb).2
    have hv : ((sources) b v).source.weight ((x b).2 v) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) v (Finset.mem_univ v)
    have he := allocatedPrincipalSides_active B U basis S j i hactive b v
    have hbound := containedProgressionCoordinate_bound (c ⟨⟨j,Sum.inr i⟩,b,v⟩)
      (hsubset ⟨⟨j,Sum.inr i⟩,b,v⟩) ((x b).2 v) (((sources) b v).source_cube _ hv) a
    rw [he] at hbound
    exact hbound
  have hgamma := principalProfileSize_pos (hR j)
    (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  exact weightedAffineModerateIntegerJetSum_box_bound coeff sources lower strides S.value rows hrows
    (by positivity) (Nat.cast_nonneg _) (fun _ =>
      (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).2) shift x hcoord t

theorem allocatedSupportedSlicedPointApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := ((torus : ℝ) / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := (torus : ℝ) ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ) -
          (normalizedSupportPlateau radius (fun t => ((z t : ℝ) - shift t) / height) : ℂ) *
            weightedAffineModerateGridApproximation coeff sources lower strides height M rows
              (fun _ => 0) shift z F‖ ≤ ε := by
  intro V t W F
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  obtain ⟨hF, he⟩ := allocatedSupportedSlicedGridDensity_approximation_on_cover_s2
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hactive hsize
    hgrid hδ hlength hstep A hA P hcP hsP hstride (Nat.cast_nonneg torus) hMK rows hrows hB hε hε1
  refine ⟨hF, fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source_s2 B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw height M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) height M z =
      allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have he' := (he shift z).trans (mul_le_of_le_one_left hε.le hscale)
  rw [← hd'] at he'
  have hgamma := principalProfileSize_pos (hR j)
    (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  have hp := integerGridDensity_plateau_transfer (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    shift z (blockJetScaleBound_nonneg _ _ _ (by positivity)) (basisAxisScale_pos (basis j) i) hM
    (fun x hx t => allocatedSupportedSlicedSource_support B U basis hR S q hq r H step c hH hsubset
      j i hactive hsize rows hrows shift x hx t) _ hε.le he'
  simpa only [hlaw, Fintype.card_coe] using hp

end Erdos3.VectorPolynomial

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

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

theorem allocatedSupportedSlicedPhysicalGridApproximation_error_s2_oai
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := ((torus : ℝ) / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := (torus : ℝ) ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
    (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
    ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ) -
        allocatedSupportedSlicedPhysicalGridApproximation B U basis hR hσ S q hq r H step c hH j i
          hactive hsize M rows F z‖ ≤ ε := by
  intro V t W F
  obtain ⟨hF, he⟩ := allocatedSupportedSlicedPointApproximation_error B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hactive hsize hgrid hδ hlength hstep A hA P hcP hsP hstride hM rows hrows hB hε hε1
  refine ⟨hF, fun x z => ?_⟩
  unfold allocatedSupportedSlicedPhysicalGridPMF allocatedSupportedSlicedPhysicalGridApproximation
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U basis hR hσ S q r H step c
    hH hsubset hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro zeta
  exact he (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridApproximation_error_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridApproximation_error_s2_oai.{u_1, u_2, u_3, u_4, u_5}
