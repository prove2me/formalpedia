-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactivePointApproximation_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T17:18:14.940005+00:00
-- url     : https://prove2.me/submissions/a4578c08-cfea-4a8d-9ecb-b37453f143f0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveGridDensity_approximation
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_axis_integer_law

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

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

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

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

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
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

open scoped BigOperators

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

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

end IntegerSourceLaw

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

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ}
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePrincipalPMF
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1)) (a : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a) =
    PMF.pure (inactivePrincipalCoefficient (basisAxisScale (b j) i)
      (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card))) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ∈
      layerIntegerPrincipalSlots (G := G) B j i := (mem_principalCoefficientSlots _ _ _).mpr ⟨a, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    exact (layerIntegerPrincipalSlots_not_constant B j i) (he ▸ hmem)
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · exact integerAxisPrincipalPMF_inactive (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) i) S.positive (principalProfileSize_pos (hR j) _) (S.gap j i) hsmall
  · exact False.elim (hp hmem)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affineWeightedCubeIntegerSum_box_bound
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (T : ℕ) (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n + 1)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : (T : ℝ) ^ (n + 1) ≤ A * K)
    (shift : rows → ℤ) (x : ∀ b j, IntegerScalarCubeBox I (s b j).length)
    (hcoord : ∀ b j i,
      |affineIntegerCubeCoordinates (u b j) (v b j) (fun i => (x b j i : ℤ)) i| ≤ T)
    (t : rows) :
    |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) A * K := by
  have hs : |affineWeightedCubeIntegerSum s u v rows shift x t - shift t| ≤
      ∑ _b : B, (2 : ℤ) ^ t.val.card *
        ∏ _j : Fin (n + 1), ((Fintype.card I + 1 : ℕ) : ℤ) * T := by
    simp only [affineWeightedCubeIntegerSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun b _ =>
      integerBooleanBlockJet_bound _ (fun _ => T) (fun j i => hcoord b j i) t)
  have hs' : |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
      ∑ _b : B, (2 : ℝ) ^ t.val.card *
        (((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (T : ℝ) ^ (n + 1)) := by
    have hh : |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
        ∑ _b : B, (2 : ℝ) ^ t.val.card *
          ∏ _j : Fin (n + 1), ((Fintype.card I + 1 : ℕ) : ℝ) * T := by exact_mod_cast hs
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
  apply hs'.trans
  calc
    _ ≤ ∑ _b : B, (2 : ℝ) ^ (n + 1) * ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      rw [← mul_assoc]
      apply (mul_le_mul_of_nonneg_left hvol (by positivity)).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hrows t t.property)) (by positivity))
        (mul_nonneg hA hK)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_unit_block_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF.map
      (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z b v k : ℤ)) t) =
      (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
        integerBooleanBlockJet (fun v k => (y ⟨a,b,v⟩ k : ℤ)) t) := by
  intro sources
  have houter :
      (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF =
        dependentProductPMF (fun b => (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi _
  have hinner (b : B a) : (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF =
      dependentProductPMF (fun v => (sources b v).source.toPMF) := FiniteProbabilityWeights.toPMF_pi _
  rw [houter]
  simp_rw [hinner]
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v => (sources b v).source.toPMF))
    (fun b z v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z v k : ℤ))
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    p.map (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet (z b) t))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize)
  rw [← hm] at hp
  simp only [PMF.map_comp, Function.comp_def] at hp
  exact hp.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

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

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedInactiveResidueJetPMF_source
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (hlarge : 2 * inactiveDenominator
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) ≤ basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r ⟨j,Sum.inr i⟩ hsize
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) => step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedCubeIntegerSource sources).toPMF.map (affineWeightedCubeIntegerSum sources lower strides rows shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  intro sources lower strides
  have hcoeff : (dependentProductPMF (fun a : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a))) =
      PMF.pure (fun _ : B ⟨j, Sum.inr i⟩ => (1 : ℤ)) := by
    ext c
    rw [dependentProductPMF_apply]
    simp_rw [allocatedInactivePrincipalPMF B U basis S j i hR hσ hsmall, inactivePrincipal_large hlarge]
    by_cases hc : c = fun _ => (1 : ℤ)
    · subst c
      simp
    · obtain ⟨a, ha⟩ : ∃ a, c a ≠ 1 := by
        by_contra hn
        apply hc
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hc]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  unfold allocatedSupportedSlicedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  simp only [one_mul]
  exact containedSupportedProgressionLaw_unit_block_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
    hH hsubset q hq r hcell ⟨j,Sum.inr i⟩ hsize rows shift

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveFixedCap
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

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

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

include hsubset in
theorem allocatedSupportedSlicedInactiveSource_support
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree) (shift : rows → ℤ)
    (x : ∀ b v, IntegerScalarCubeBox α ((sources) b v).length)
    (hx : (weightedCubeIntegerSource sources).weight x ≠ 0) (t : rows) :
    |(affineWeightedCubeIntegerSum sources lower strides rows shift x t : ℝ) - shift t| ≤ radius * height := by
  let _ : ∀ index, DecidableEq (I index) := inferInstance
  have hcoord (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) (a : Option α) :
      |affineIntegerCubeCoordinates (lower b v) (strides b v) (fun a => (x b v a : ℤ)) a| ≤ side := by
    have hb : (FiniteProbabilityWeights.pi (fun v => ((sources) b v).source)).weight (x b) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
    have hprod : (∏ v, ((sources) b v).source.weight (x b v)) ≠ 0 := hb
    have hv := (Finset.prod_ne_zero_iff.mp hprod) v (Finset.mem_univ v)
    have he : allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
      rw [layerIntegerPrincipalSlots_card]
      change integerAxisSideLength degree height S.value
        (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
      simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]
    have hbnd := containedProgressionCoordinate_bound (c ⟨⟨j,Sum.inr i⟩,b,v⟩)
      (hsubset ⟨⟨j,Sum.inr i⟩,b,v⟩) (x b v) (((sources) b v).source_cube _ hv) a
    rw [he] at hbnd
    exact hbnd
  have hvol : (side : ℝ) ^ degree ≤ 1 * (height : ℝ) := by
    rw [one_mul]
    exact_mod_cast (inactiveSideLength_power (Nat.zero_lt_succ _) hlarge).trans (Nat.div_le_self _ _)
  exact affineWeightedCubeIntegerSum_box_bound sources lower strides side rows hrows
    zero_le_one (Nat.cast_nonneg _) hvol shift x hcoord t

theorem allocatedSupportedSlicedInactivePointApproximation_error
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
    ∀ shift z : rows → ℤ,
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ) -
        (normalizedSupportPlateau radius (fun t => ((z t : ℝ) - shift t) / height) : ℂ) *
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ε := by
  intro V t W ζ F
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  obtain ⟨hF, hcap, he⟩ := allocatedSupportedSlicedInactiveGridDensity_approximation B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride
    (Nat.cast_nonneg torus) hMK rows hrows hB hε hε1
  refine ⟨hF, hcap, fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsmall hlarge hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedCubeIntegerSource sources)
    (affineWeightedCubeIntegerSum sources lower strides rows shift) _ hlaw height M z
  have hd' : integerGridDensity (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z =
      allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have he' := (he shift z).trans (mul_le_of_le_one_left hε.le hscale)
  rw [← hd'] at he'
  have hp := integerGridDensity_plateau_transfer (weightedCubeIntegerSource sources)
    (affineWeightedCubeIntegerSum sources lower strides rows shift) shift z
    (blockJetScaleBound_nonneg _ _ _ zero_le_one) (basisAxisScale_pos (basis j) i) hM
    (fun x hx t => allocatedSupportedSlicedInactiveSource_support B U basis S q hq r H step c hH hsubset
      j i hsize hsmall hlarge rows hrows shift x hx t) _ hε.le he'
  simpa only [hlaw, Fintype.card_coe] using hp

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

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

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactivePointApproximation_error.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactivePointApproximation_error.{u_1, u_2, u_3, u_4, u_5}
