-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.low_information_joining
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:11:05.900502+00:00
-- url     : https://prove2.me/submissions/6636689f-e749-47ee-b3b7-539ded40eb13

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Joining.lean:L83-L109
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.low_information_joining. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Definitions.Def_OAI_InformationTheory_SoftChannel_Payment
import Definitions.Def_OAI_InformationTheory_SoftChannel_HighReserve
import Definitions.Def_OAI_InformationTheory_SoftChannel_RateSlope
import Definitions.Def_OAI_InformationTheory_SoftChannel_Wall
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_common_output_payment
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_exists_reflected_entropy
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_normalizedEntropy_actual
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_normalizedEntropy_tangent
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_r_pairEntropyGap_le_pairDissipation
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_wall_comparison

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem entropy_nonneg {v : ℝ} (hv : v ∈ Icc (-1) 1) : 0 ≤ entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg (by linarith [hv.1]) (by linarith [hv.2])

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_sub (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x - h x) = cubeAverage g - cubeAverage h := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

theorem cubeAverage_smul (c : ℝ) (g : Cube n → ℝ) :
    cubeAverage (fun x => c * g x) = c * cubeAverage g := by
  simp [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

theorem cubeAverage_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    cubeAverage g ≤ cubeAverage h := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x)
    (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_strict_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x)
    (hlt : ∃ x, g x < h x) : cubeAverage g < cubeAverage h := by
  apply (div_lt_div_iff_of_pos_right (cube_denominator_pos n)).2
  apply Finset.sum_lt_sum (fun x _ => hgh x)
  obtain ⟨x, hx⟩ := hlt
  exact ⟨x, Finset.mem_univ x, hx⟩

theorem cubeAverage_lt {g h : Cube n → ℝ} (hgh : ∀ x, g x < h x) :
    cubeAverage g < cubeAverage h := by
  exact cubeAverage_strict_mono (fun x => (hgh x).le) ⟨fun _ => false, hgh _⟩

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PairEntropy ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a + b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h)

theorem pair_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a - b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.MonotoneDissipation ----
namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

theorem IsInterior.entropyAverage_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < entropyAverage g := by
  have h := cubeAverage_lt (fun x => entropy_pos (hg x))
  simpa only [cubeAverage_const, entropyAverage] using h

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Canonical ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma bose_pos {z : ℝ} (hz : 0 < z) : 0 < bose z := by
  exact inv_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz))

lemma exp_neg_lt_one {z : ℝ} (hz : 0 < z) : Real.exp (-z) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr hz)

lemma bose_eq_exp_neg {z : ℝ} (hz : 0 < z) :
    bose z = Real.exp (-z) / (1 - Real.exp (-z)) := by
  have he := (Real.one_lt_exp_iff.mpr hz : 1 < Real.exp z)
  rw [Real.exp_neg]
  unfold bose
  field_simp

lemma hasDerivAt_bose {z : ℝ} (hz : 0 < z) :
    HasDerivAt bose (-(bose z * (bose z + 1))) z := by
  have he : Real.exp z - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz))
  convert! (((Real.hasDerivAt_exp z).sub_const 1).inv he) using 1
  unfold bose
  field_simp
  ring

lemma exp_pair (z w : ℝ) (i j : ℕ) :
    Real.exp (-((i : ℝ) * z + (j : ℝ) * w)) =
      Real.exp (-z) ^ i * Real.exp (-w) ^ j := by
  rw [show -((i : ℝ) * z + (j : ℝ) * w) = (i : ℝ) * (-z) + (j : ℝ) * (-w) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]

lemma geom_positive_sum {x : ℝ} (hx : x ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ (i + 1) = x / (1 - x) * (1 - x ^ n) := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq hx]
  field_simp
  ring

lemma canonicalGroup_eq {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (k : ℕ) :
    canonicalGroup z w k =
      bose w * (Real.exp (-z) ^ (k + 1) / (k + 1 : ℕ)) +
      bose z * (Real.exp (-w) ^ (k + 1) / (k + 1 : ℕ)) -
      (1 + bose z + bose w) * ((Real.exp (-z) * Real.exp (-w)) ^ (k + 1) /
        (k + 1 : ℕ)) := by
  have hz1 := (exp_neg_lt_one hz).ne
  have hw1 := (exp_neg_lt_one hw).ne
  unfold canonicalGroup
  simp_rw [exp_pair, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [geom_positive_sum hw1, geom_positive_sum hz1,
    bose_eq_exp_neg hz, bose_eq_exp_neg hw]
  simp only [mul_pow, pow_succ]
  field_simp
  ring

lemma hasSum_canonicalGroup {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    HasSum (canonicalGroup z w)
      ((1 + bose z + bose w) * Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        bose w * Real.log (1 - Real.exp (-z)) -
        bose z * Real.log (1 - Real.exp (-w))) := by
  have hx : |Real.exp (-z)| < 1 := by rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one hz
  have hy : |Real.exp (-w)| < 1 := by rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one hw
  have hxy : |Real.exp (-z) * Real.exp (-w)| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Real.exp (-z)), abs_nonneg (Real.exp (-w))]
  convert! (((Real.hasSum_pow_div_log_of_abs_lt_one hx).mul_left (bose w)).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left (bose z))).sub
    ((Real.hasSum_pow_div_log_of_abs_lt_one hxy).mul_left (1 + bose z + bose w)) using 1
  · ext k
    simpa only [Nat.cast_add, Nat.cast_one] using canonicalGroup_eq hz hw k
  · ring

lemma log_bose {z : ℝ} (hz : 0 < z) :
    Real.log (bose z) = -z - Real.log (1 - Real.exp (-z)) := by
  rw [bose_eq_exp_neg hz, Real.log_div (Real.exp_ne_zero _)
    (ne_of_gt (sub_pos.mpr (exp_neg_lt_one hz))), Real.log_exp]

lemma log_bose_add_one {z : ℝ} (hz : 0 < z) :
    Real.log (bose z + 1) = -Real.log (1 - Real.exp (-z)) := by
  rw [bose_eq_exp_neg hz]
  have he := (sub_pos.mpr (exp_neg_lt_one hz)).ne'
  rw [show Real.exp (-z) / (1 - Real.exp (-z)) + 1 =
    (1 - Real.exp (-z))⁻¹ by field_simp; ring, Real.log_inv]

lemma log_one_add_bose_add_bose {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    Real.log (1 + bose z + bose w) =
      Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        Real.log (1 - Real.exp (-z)) - Real.log (1 - Real.exp (-w)) := by
  have hx := (sub_pos.mpr (exp_neg_lt_one hz)).ne'
  have hy := (sub_pos.mpr (exp_neg_lt_one hw)).ne'
  have hxy : 0 < 1 - Real.exp (-z) * Real.exp (-w) := by
    have hz1 := exp_neg_lt_one hz
    have hw1 := exp_neg_lt_one hw
    nlinarith [Real.exp_pos (-z), Real.exp_pos (-w)]
  rw [bose_eq_exp_neg hz, bose_eq_exp_neg hw]
  rw [show 1 + Real.exp (-z) / (1 - Real.exp (-z)) +
    Real.exp (-w) / (1 - Real.exp (-w)) =
    (1 - Real.exp (-z) * Real.exp (-w)) / ((1 - Real.exp (-z)) * (1 - Real.exp (-w))) by
      field_simp; ring]
  rw [Real.log_div hxy.ne' (mul_ne_zero hx hy), Real.log_mul hx hy]
  ring

lemma normalizedEntropy_series_identity {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    normalizedEntropy z w = (canonicalQ z + canonicalQ w) / 2 +
      ((1 + bose z + bose w) * Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        bose w * Real.log (1 - Real.exp (-z)) -
        bose z * Real.log (1 - Real.exp (-w))) := by
  unfold normalizedEntropy canonicalQ
  dsimp only
  rw [log_bose hz, log_bose hw, log_bose_add_one hz, log_bose_add_one hw,
    log_one_add_bose_add_bose hz hw]
  ring

lemma hasSum_normalizedEntropy {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    HasSum (canonicalGroup z w)
      (normalizedEntropy z w - (canonicalQ z + canonicalQ w) / 2) := by
  rw [normalizedEntropy_series_identity hz hw]
  convert! hasSum_canonicalGroup hz hw using 1; ring

lemma normalizedEntropy_symm (z w : ℝ) : normalizedEntropy z w = normalizedEntropy w z := by
  unfold normalizedEntropy
  dsimp only
  rw [show 1 + bose w + bose z = 1 + bose z + bose w by ring]
  ring

lemma normalizedEntropyDz_neg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    normalizedEntropyDz z w < 0 := by
  have hu := bose_pos hz
  have hv := bose_pos hw
  have h₁ := Real.log_lt_log (by linarith : 0 < bose z + 1)
    (show bose z + 1 < 1 + bose z + bose w by linarith)
  have h₂ := Real.log_lt_log hu (show bose z < 1 + bose z + bose w by linarith)
  unfold normalizedEntropyDz
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hu) (by linarith))
    (by linarith)

lemma normalizedEntropyDz_order {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    normalizedEntropyDz z w ≤ normalizedEntropyDz w z := by
  rcases hzw.eq_or_lt with rfl | hzw
  · rfl
  · have ht := normalizedEntropy_tangent hz hw hw hz
    rw [normalizedEntropy_symm w z] at ht
    nlinarith

lemma hasDerivAt_bose_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => -(bose t * (bose t + 1)))
      (bose z * (bose z + 1) * (2 * bose z + 1)) z := by
  convert! ((hasDerivAt_bose hz).mul ((hasDerivAt_bose hz).add_const 1)).neg using 1; ring

lemma convexOn_bose : ConvexOn ℝ (Ioi 0) bose := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun z hz => (hasDerivAt_bose hz).continuousAt.continuousWithinAt)
    (f' := fun z => -(bose z * (bose z + 1)))
    (f'' := fun z => bose z * (bose z + 1) * (2 * bose z + 1))
  · intro z hz
    exact (hasDerivAt_bose (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (hasDerivAt_bose_deriv (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    have hb := bose_pos (show 0 < z by simpa using hz)
    positivity

lemma bose_tangent {z Z : ℝ} (hz : 0 < z) (hZ : 0 < Z) :
    bose z - bose z * (bose z + 1) * (Z-z) ≤ bose Z := by
  rcases lt_trichotomy z Z with hlt | rfl | hgt
  · have h := convexOn_bose.le_slope_of_hasDerivAt hz hZ hlt (hasDerivAt_bose hz)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith
  · simp
  · have h := convexOn_bose.slope_le_of_hasDerivAt hZ hz hgt (hasDerivAt_bose hz)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith

lemma canonicalPrice_pos {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    0 < canonicalPrice z w := by
  unfold canonicalPrice
  exact neg_pos.mpr (inv_neg''.mpr (mul_neg_of_pos_of_neg (by norm_num) (normalizedEntropyDz_neg hz hw)))

lemma canonicalPrice_gradient {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    1/8 + canonicalPrice z w * normalizedEntropyDz z w = 0 := by
  unfold canonicalPrice
  have h := (normalizedEntropyDz_neg hz hw).ne
  field_simp
  ring

lemma canonicalGamma_nonneg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    0 ≤ canonicalGamma z w := by
  have horder := mul_le_mul_of_nonneg_left (normalizedEntropyDz_order hz hw hzw)
    (canonicalPrice_pos hz hw).le
  have hzero := canonicalPrice_gradient hz hw
  unfold canonicalGamma
  apply div_nonneg (by linarith)
  have h := bose_pos hw
  positivity

lemma canonicalGamma_gradient {z w : ℝ} (_hz : 0 < z) (hw : 0 < w) :
    1/8 + canonicalPrice z w * normalizedEntropyDz w z =
      2 * canonicalGamma z w * bose w * (bose w + 1) := by
  unfold canonicalGamma
  have h := (bose_pos hw).ne'
  have h₁ : bose w + 1 ≠ 0 := by linarith [bose_pos hw]
  field_simp

lemma canonicalGamma_self {z : ℝ} (hz : 0 < z) : canonicalGamma z z = 0 := by
  unfold canonicalGamma
  rw [canonicalPrice_gradient hz hz, zero_div]

lemma canonical_support_normalized {z w Z W : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) (hZ : 0 < Z) (hW : 0 < W) :
    (z+w)/8 + canonicalPrice z w * normalizedEntropy z w +
      canonicalGamma z w * (1 + 2*bose w) ≤
    (Z+W)/8 + canonicalPrice z w * normalizedEntropy Z W +
      canonicalGamma z w * (1 + 2*bose W) := by
  have h₁ := mul_le_mul_of_nonneg_left (normalizedEntropy_tangent hz hw hZ hW)
    (canonicalPrice_pos hz hw).le
  have h₂ := mul_le_mul_of_nonneg_left (bose_tangent hw hW)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (canonicalGamma_nonneg hz hw hzw))
  have hzG := canonicalPrice_gradient hz hw
  have hwG := canonicalGamma_gradient hz hw
  nlinarith [congrArg (fun q : ℝ => q * (Z-z)) hzG,
    congrArg (fun q : ℝ => q * (W-w)) hwG]

lemma joiningZ_pos {x y : ℝ} (hy : -1 < y) (hxy : y < x) : 0 < joiningZ x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1+y)).mpr
  linarith

lemma joiningW_pos {x y : ℝ} (hx : x < 1) (hxy : y < x) : 0 < joiningW x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1-x)).mpr
  linarith

lemma bose_joiningW {x y : ℝ} (hx : x < 1) (hxy : y < x) :
    bose (joiningW x y) = (1-x)/(x-y) := by
  have hp : 0 < (1-y)/(1-x) := div_pos (by linarith) (by linarith)
  unfold bose joiningW
  rw [Real.exp_log hp]
  have hd : 1-x ≠ 0 := by linarith
  rw [show (1-y)/(1-x)-1=(x-y)/(1-x) by field_simp; ring, inv_div]

lemma joining_order {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) (hm : 0 ≤ x+y) : joiningZ x y ≤ joiningW x y := by
  apply Real.log_le_log (div_pos (by linarith [hx.1]) (by linarith [hy.1]))
  apply (div_le_div_iff₀ (by linarith [hy.1] : 0 < 1+y) (by linarith [hx.2] : 0 < 1-x)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy.le) hm]

lemma joiningCost_coordinates {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    joiningCost x y = (x-y)*(joiningZ x y + joiningW x y)/8 := by
  unfold joiningCost joiningZ joiningW
  rw [artanh_eq_log_sub hx, artanh_eq_log_sub hy,
    Real.log_div (by linarith [hx.1]) (by linarith [hy.1]),
    Real.log_div (by linarith [hy.2]) (by linarith [hx.2])]
  ring

lemma joiningCost_nonneg {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    0 ≤ joiningCost x y := by
  unfold joiningCost
  rcases le_total y x with h | h
  · apply mul_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))
    exact sub_nonneg.mpr (Real.strictMonoOn_artanh.monotoneOn hy hx h)
  · apply mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by norm_num))
    exact sub_nonpos.mpr (Real.strictMonoOn_artanh.monotoneOn hx hy h)

lemma normalizedEntropy_nonneg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    0 ≤ normalizedEntropy z w := by
  have hgroups : 0 ≤ normalizedEntropy z w - (canonicalQ z + canonicalQ w)/2 := by
    apply hasSum_le (g := canonicalGroup z w) _ hasSum_zero (hasSum_normalizedEntropy hz hw)
    intro n
    unfold canonicalGroup
    positivity
  have hq (t : ℝ) (ht : 0 < t) : 0 ≤ canonicalQ t := by
    unfold canonicalQ
    have hlog : Real.log (1-Real.exp (-t)) ≤ 0 :=
      Real.log_nonpos (by linarith [exp_neg_lt_one ht]) (by linarith [Real.exp_pos (-t)])
    nlinarith [bose_pos ht]
  linarith [hq z hz, hq w hw]

lemma coreKappa_pos {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    0 < coreKappa z w := by
  have h₁ := mul_nonneg (canonicalPrice_pos hz hw).le (normalizedEntropy_nonneg hz hw)
  have h₂ := mul_nonneg (canonicalGamma_nonneg hz hw hzw) (by linarith [bose_pos hw] : 0 ≤ 1+2*bose w)
  unfold coreKappa
  linarith

lemma canonical_support {z w A B : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w)
    (hA : A ∈ Ioo (-1) 1) (hB : B ∈ Ioo (-1) 1) :
    coreKappa z w * (A-B) ≤ joiningCost A B +
      canonicalPrice z w * (entropy A + entropy B) + canonicalGamma z w * (2-A-B) := by
  by_cases hAB : B < A
  · have h := canonical_support_normalized hz hw hzw (joiningZ_pos hB.1 hAB) (joiningW_pos hA.2 hAB)
    have hh := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hAB.le)
    rw [normalizedEntropy_actual hA hB hAB, bose_joiningW hA.2 hAB] at hh
    change coreKappa z w * (A-B) ≤ _ at hh
    rw [joiningCost_coordinates hA hB]
    convert! hh using 1
    have hd : A-B ≠ 0 := ne_of_gt (sub_pos.mpr hAB)
    field_simp
    ring
  · have hleft := mul_nonpos_of_nonneg_of_nonpos (coreKappa_pos hz hw hzw).le
      (sub_nonpos.mpr (le_of_not_gt hAB))
    have hcost := joiningCost_nonneg hA hB
    have hent := mul_nonneg (canonicalPrice_pos hz hw).le
      (add_nonneg (entropy_nonneg ⟨hA.1.le,hA.2.le⟩) (entropy_nonneg ⟨hB.1.le,hB.2.le⟩))
    have hcorner := mul_nonneg (canonicalGamma_nonneg hz hw hzw)
      (show 0 ≤ 2-A-B by linarith [hA.2,hB.2])
    linarith

lemma canonical_core_contact {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) :
    coreKappa (joiningZ x y) (joiningW x y) * (x-y) = joiningCost x y +
      canonicalPrice (joiningZ x y) (joiningW x y) * (entropy x+entropy y) +
      canonicalGamma (joiningZ x y) (joiningW x y) * (2-x-y) := by
  unfold coreKappa
  rw [normalizedEntropy_actual hx hy hxy, bose_joiningW hx.2 hxy, joiningCost_coordinates hx hy]
  have hd : x-y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  field_simp
  ring

lemma averaged_canonical_support {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) {z w : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    coreKappa z w * (cubeAverage A-cubeAverage B) ≤
      cubeAverage (fun t => joiningCost (A t) (B t)) +
      canonicalPrice z w * (entropyAverage A+entropyAverage B) +
      canonicalGamma z w * (2-cubeAverage A-cubeAverage B) := by
  have h := cubeAverage_mono (fun t => canonical_support hz hw hzw (hA t) (hB t))
  simpa only [cubeAverage_add, cubeAverage_sub, cubeAverage_smul, cubeAverage_const,
    entropyAverage] using h

lemma canonical_core_lower {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) {x y k : ℝ}
    (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) (hxy : y < x) (hm : 0 ≤ x+y)
    (hd : cubeAverage A-cubeAverage B = k*(x-y))
    (he : entropyAverage A+entropyAverage B = k*(entropy x+entropy y))
    (hc : canonicalGamma (joiningZ x y) (joiningW x y) *
      (2-cubeAverage A-cubeAverage B) =
      k*canonicalGamma (joiningZ x y) (joiningW x y)*(2-x-y)) :
    k * joiningCost x y ≤ cubeAverage (fun t => joiningCost (A t) (B t)) := by
  have h := averaged_canonical_support A B hA hB (joiningZ_pos hy.1 hxy) (joiningW_pos hx.2 hxy)
    (joining_order hx hy hxy hm)
  rw [hd, he, hc] at h
  have heq := congrArg (fun q : ℝ => k*q) (canonical_core_contact hx hy hxy)
  nlinarith

lemma onecorner_domain {m d k : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (hk : k ∈ Icc (1-m) 1) :
    onecornerX m d k ∈ Ioo (-1) 1 ∧ onecornerY m d k ∈ Ioo (-1) 1 ∧
      onecornerY m d k < onecornerX m d k ∧ 0 ≤ onecornerX m d k+onecornerY m d k := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hL : 0 < (1-m-d)/k := div_pos (by linarith) hk0
  have hU : (1-m+d)/k < 2 := (div_lt_iff₀ hk0).mpr (by linarith [hk.1])
  have hXY : (1-m-d)/k < (1-m+d)/k := (div_lt_div_iff_of_pos_right hk0).mpr (by linarith)
  have hsum : (1-m-d)/k+(1-m+d)/k ≤ 2 := by
    rw [← add_div]
    exact (div_le_iff₀ hk0).mpr (by linarith [hk.1])
  unfold onecornerX onecornerY
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,by linarith,by linarith⟩

lemma onecorner_means {m d k : ℝ} (hk : k ≠ 0) :
    m+d = 1-k+k*onecornerX m d k ∧ m-d = 1-k+k*onecornerY m d k := by
  unfold onecornerX onecornerY
  constructor <;> field_simp <;> ring

lemma onecorner_entropy_left {m d : ℝ} (hm : m < 1) :
    onecornerEntropy m d (1-m) = (1-m)*entropy (d/(1-m)) := by
  have hm0 : 1-m ≠ 0 := by linarith
  unfold onecornerEntropy onecornerX onecornerY
  rw [show 1-(1-m-d)/(1-m)=d/(1-m) by field_simp; ring,
    show 1-(1-m+d)/(1-m)=-(d/(1-m)) by field_simp; ring, entropy_neg]
  ring

lemma onecorner_entropy_right (m d : ℝ) :
    onecornerEntropy m d 1 = (entropy (m+d)+entropy (m-d))/2 := by
  unfold onecornerEntropy onecornerX onecornerY
  ring_nf

lemma continuousOn_onecornerEntropy {m d : ℝ} (hm : m < 1) :
    ContinuousOn (onecornerEntropy m d) (Icc (1-m) 1) := by
  intro k hk
  have hk0 : k ≠ 0 := by linarith [hk.1]
  unfold onecornerEntropy onecornerX onecornerY
  have h₁ : ContinuousAt (fun k : ℝ => 1-(1-m-d)/k) k := by fun_prop
  have h₂ : ContinuousAt (fun k : ℝ => 1-(1-m+d)/k) k := by fun_prop
  exact ((continuousAt_id.mul ((continuous_entropy.continuousAt.comp h₁).add
    (continuous_entropy.continuousAt.comp h₂))).div_const 2).continuousWithinAt

lemma exists_onecorner_entropy {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (he0 : (1-m)*entropy (d/(1-m)) ≤ e)
    (he1 : e ≤ (entropy (m+d)+entropy (m-d))/2) :
    ∃ k ∈ Icc (1-m) 1, onecornerEntropy m d k = e := by
  apply intermediate_value_Icc (by linarith : 1-m ≤ 1) (continuousOn_onecornerEntropy (by linarith))
  simpa only [onecorner_entropy_left (by linarith : m<1), onecorner_entropy_right] using ⟨he0,he1⟩

lemma onecorner_cost_lower {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d k : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1) (hk : k ∈ Icc (1-m) 1)
    (ha : cubeAverage A = m+d) (hb : cubeAverage B = m-d)
    (he : (entropyAverage A+entropyAverage B)/2 = onecornerEntropy m d k) :
    k*joiningCost (onecornerX m d k) (onecornerY m d k) ≤
      cubeAverage (fun t => joiningCost (A t) (B t)) := by
  obtain ⟨hx,hy,hxy,hcenter⟩ := onecorner_domain hm hd hmd hk
  have hk0 : k ≠ 0 := by linarith [hk.1]
  obtain ⟨hamean,hbmean⟩ := onecorner_means (m := m) (d := d) hk0
  apply canonical_core_lower A B hA hB hx hy hxy hcenter
  · rw [ha,hb]; nlinarith
  · unfold onecornerEntropy at he; linarith
  · rw [ha,hb]
    rw [hamean,hbmean]
    ring

lemma reflected_cost_lower {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {r k : ℝ} (hr : r ∈ Ioo 0 1)
    (hd : cubeAverage A-cubeAverage B = 2*k*r)
    (he : (entropyAverage A+entropyAverage B)/2 = k*entropy r) :
    k*joiningCost r (-r) ≤ cubeAverage (fun t => joiningCost (A t) (B t)) := by
  have hx : r ∈ Ioo (-1) 1 := ⟨by linarith [hr.1],hr.2⟩
  have hy : -r ∈ Ioo (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hzw : joiningZ r (-r) = joiningW r (-r) := by simp [joiningZ,joiningW,sub_eq_add_neg]
  have hc : canonicalGamma (joiningZ r (-r)) (joiningW r (-r)) = 0 := by
    rw [← hzw]
    exact canonicalGamma_self (joiningZ_pos hy.1 (by linarith [hr.1]))
  apply canonical_core_lower A B hA hB hx hy (by linarith [hr.1]) (by linarith)
  · rw [hd]; ring
  · rw [entropy_neg]; linarith
  · rw [hc]; ring

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Payment ----
namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma thinX_add (c d l : ℝ) : thinX c l+l*d=thinX (c+d) l := by unfold thinX; ring
lemma thinX_sub (c d l : ℝ) : thinX c l-l*d=thinX (c-d) l := by unfold thinX; ring

lemma entropy_thinX_strict {a l : ℝ} (ha : a ∈ Ioo (-1) 1) (hl : l ∈ Ioo (0:ℝ) 1) :
    l*entropy a < entropy (thinX a l) := by
  have hap : (1+a)/2 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [ha.1,ha.2]
  have h := Real.strictConcave_binEntropy.2 (by norm_num : (1:ℝ) ∈ Icc 0 1) hap
    (by linarith [ha.2] : (1:ℝ) ≠ (1+a)/2) (by linarith [hl.2] : 0 < 1-l) hl.1
    (by ring : 1-l+l=1)
  rw [entropy_eq_binEntropy,entropy_eq_binEntropy]
  simp only [smul_eq_mul,Real.binEntropy_one,mul_zero,zero_add,mul_one] at h
  convert! h using 1
  congr 1
  unfold thinX
  ring

lemma thinJ_pos {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : 0 < thinJ c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_nonneg hd]; exact hcd
  have h₁ := entropy_thinX_strict (pair_add_mem_Ioo c d hh) hl
  have h₂ := entropy_thinX_strict (pair_sub_mem_Ioo c d hh) hl
  dsimp [thinJ,pairH]
  rw [thinX_add,thinX_sub]
  linarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Wall ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma wall_domain {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : |m|+|d|<1 := by
  rwa [abs_of_nonneg hm,abs_of_nonneg hd]

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Joining ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma joiningCost_pair (c d : ℝ) : joiningCost (c+d) (c-d) = pairDissipation c d := by
  unfold joiningCost pairDissipation
  ring

lemma onecorner_payment {m d k : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d<1)
    (hk : k ∈ Icc (1-m) 1) :
    wallDemand m d (onecornerEntropy m d k) ≤ k*joiningCost (onecornerX m d k) (onecornerY m d k) := by
  have hk0 : 0 < k := by linarith [hk.1]
  let c := 1-(1-m)/k
  let v := d/k
  have hc : 0 ≤ c := by dsimp [c]; exact sub_nonneg.mpr ((div_le_one hk0).mpr hk.1)
  have hv : 0 < v := div_pos hd hk0
  have hcv : c+v<1 := by
    dsimp [c,v]
    rw [show 1-(1-m)/k+d/k=1-(1-m-d)/k by ring]
    exact sub_lt_self _ (div_pos (by linarith : 0<1-m-d) hk0)
  have hx : c+v=onecornerX m d k := by dsimp [c,v,onecornerX]; ring
  have hy : c-v=onecornerY m d k := by dsimp [c,v,onecornerY]; ring
  have hthin : thinX c k=m := by dsimp [thinX,c]; field_simp; ring
  have hkv : k*v=d := by dsimp [v]; field_simp
  have he : k*pairH c v=onecornerEntropy m d k := by dsimp [pairH,onecornerEntropy]; rw [hx,hy]; ring
  have h := common_output_payment hc hv hcv ⟨hk0,hk.2⟩
  have hcap := mul_le_mul_of_nonneg_left
    (r_pairEntropyGap_le_pairDissipation c v (wall_domain hc hv.le hcv)) hk0.le
  have hI : thinI c v k=entropy m-onecornerEntropy m d k := by dsimp [thinI]; rw [hthin,he]
  have hJ : thinJ c v k=pairH m d-onecornerEntropy m d k := by dsimp [thinJ]; rw [hthin,he,hkv]
  rw [hI,hJ] at h
  rw [← joiningCost_pair,hx,hy] at hcap
  exact h.trans hcap

lemma high_value_joining {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d<1)
    (ha : cubeAverage A=m+d) (hb : cubeAverage B=m-d)
    (he : (1-m)*entropy (d/(1-m)) ≤ (entropyAverage A+entropyAverage B)/2)
    (hphys : (entropyAverage A+entropyAverage B)/2 ≤ pairH m d) :
    wallDemand m d ((entropyAverage A+entropyAverage B)/2) ≤
      cubeAverage (fun x => joiningCost (A x) (B x)) := by
  obtain ⟨k,hk,hke⟩ := exists_onecorner_entropy hm hd hmd he hphys
  exact (hke ▸ onecorner_payment hm hd hmd hk).trans
    (onecorner_cost_lower A B hA hB hm hd hmd hk ha hb hke.symm)

lemma reflected_payment {m r k : ℝ} (hm : 0 < m) (hr : r ∈ Ioo 0 1)
    (hk : 0 < k) (hkm : k ≤ 1-m) (hI : entropy m-k*entropy r ≤ softCutoff) :
    wallDemand m (k*r) (k*entropy r) ≤ k*joiningCost r (-r) := by
  have hk1 : k < 1 := by linarith
  have hw : 0 ≤ 1-k := by linarith
  have hd : 0 < k*r := mul_pos hk hr.1
  have hwd : (1-k)+k*r<1 := by nlinarith [mul_pos hk (sub_pos.mpr hr.2)]
  have he : 0 < k*entropy r := mul_pos hk (entropy_pos ⟨by linarith [hr.1],hr.2⟩)
  have hX : thinX 0 k=1-k := by simp [thinX]
  have hH : pairH 0 r=entropy r := by simp [pairH,entropy_neg]
  have hj := thinJ_pos (by norm_num : (0:ℝ) ≤ 0) hr.1.le (by linarith [hr.2] : 0+r<1) ⟨hk,hk1⟩
  have hje : k*entropy r < pairH (1-k) (k*r) := by
    dsimp [thinJ] at hj
    rw [hX,hH] at hj
    linarith
  have hwall := wall_comparison hm.le (by linarith : m ≤ 1-k) hd.le hwd he hje hI
  have hpay := common_output_payment (by norm_num : (0:ℝ) ≤ 0) hr.1 (by linarith [hr.2] : 0+r<1) ⟨hk,hk1.le⟩
  have hI' : thinI 0 r k=entropy (1-k)-k*entropy r := by dsimp [thinI]; rw [hX,hH]
  have hJ' : thinJ 0 r k=pairH (1-k) (k*r)-k*entropy r := by dsimp [thinJ]; rw [hX,hH]
  rw [hI',hJ'] at hpay
  have hcap := mul_le_mul_of_nonneg_left (r_pairEntropyGap_le_pairDissipation 0 r
    (by simpa only [abs_zero,zero_add,abs_of_pos hr.1] using hr.2)) hk.le
  have hcost : pairDissipation 0 r=joiningCost r (-r) := by
    simpa using (joiningCost_pair 0 r).symm
  rw [hcost] at hcap
  exact hwall.trans (hpay.trans hcap)

lemma low_information_joining {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) (hmd : m+d<1)
    (ha : cubeAverage A=m+d) (hb : cubeAverage B=m-d)
    (hphys : (entropyAverage A+entropyAverage B)/2 ≤ pairH m d)
    (hI : entropy m-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    wallDemand m d ((entropyAverage A+entropyAverage B)/2) ≤
      cubeAverage (fun x => joiningCost (A x) (B x)) := by
  by_cases he : (1-m)*entropy (d/(1-m)) ≤ (entropyAverage A+entropyAverage B)/2
  · exact high_value_joining A B hA hB hm.le hd hmd ha hb he hphys
  · have hep : 0 < (entropyAverage A+entropyAverage B)/2 := by
      linarith [hA.entropyAverage_pos,hB.entropyAverage_pos]
    obtain ⟨r,hr,hre⟩ := exists_reflected_entropy hm.le hd hmd hep (le_of_not_ge he)
    have hm1 : 0 < 1-m := by linarith
    have hr0 : 0 < r := (div_pos hd hm1).trans_le hr.1
    let k := d/r
    have hk : 0 < k := div_pos hd hr0
    have hkr : k*r=d := by dsimp [k]; field_simp
    have hkm : k ≤ 1-m := by
      apply (div_le_iff₀ hr0).mpr
      have h := (div_le_iff₀ hm1).mp hr.1
      nlinarith
    have heq : k*entropy r=(entropyAverage A+entropyAverage B)/2 := hre
    have hpay := reflected_payment hm ⟨hr0,hr.2⟩ hk hkm (by rwa [heq])
    rw [hkr,heq] at hpay
    have hcost := reflected_cost_lower A B hA hB ⟨hr0,hr.2⟩
      (show cubeAverage A-cubeAverage B=2*k*r by rw [ha,hb]; nlinarith [hkr]) heq.symm
    exact hpay.trans hcost

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.low_information_joining := @_root_.OAI.LeanBlast.CourtadeKumar.low_information_joining
