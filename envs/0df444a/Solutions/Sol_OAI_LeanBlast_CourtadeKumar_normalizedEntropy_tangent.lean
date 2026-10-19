-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:42:12.411058+00:00
-- url     : https://prove2.me/submissions/851ceb86-96cc-439d-86a6-d20b428abac9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Canonical.lean:L277-L298
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent. The node keeps its source
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

lemma hasDerivAt_canonicalQ {z : ℝ} (hz : 0 < z) :
    HasDerivAt canonicalQ (-z * bose z * (bose z + 1)) z := by
  have hneg : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-z)) z := by
    convert! (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg using 1; ring
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_bose hz)).sub
    ((hneg.const_sub 1).log (ne_of_gt (sub_pos.mpr (exp_neg_lt_one hz))))
  convert! hd using 1
  simp only [id_eq, neg_neg]
  rw [bose_eq_exp_neg hz]
  ring

lemma hasDerivAt_canonicalQ_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => -t * bose t * (bose t + 1))
      (bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1)) z := by
  convert! (((hasDerivAt_id z).neg.mul (hasDerivAt_bose hz)).mul
    ((hasDerivAt_bose hz).add_const 1)) using 1
  simp only [Pi.mul_apply, Pi.neg_apply, id_eq]
  ring

lemma canonicalQ_second_pos {z : ℝ} (hz : 0 < z) :
    0 < bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1) := by
  have hb := bose_pos hz
  apply mul_pos (mul_pos hb (by linarith))
  have hexp : 1 - z < Real.exp (-z) := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr hz.ne')
    linarith
  have he : 0 < 1 - Real.exp (-z) := sub_pos.mpr (exp_neg_lt_one hz)
  rw [bose_eq_exp_neg hz]
  rw [show z * (2 * (Real.exp (-z) / (1 - Real.exp (-z))) + 1) - 1 =
    (z * (1 + Real.exp (-z)) - (1 - Real.exp (-z))) / (1 - Real.exp (-z)) by
      field_simp; ring]
  apply div_pos _ he
  nlinarith [Real.exp_pos (-z)]

lemma convexOn_canonicalQ : ConvexOn ℝ (Ioi 0) canonicalQ := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun z hz => (hasDerivAt_canonicalQ hz).continuousAt.continuousWithinAt)
    (f' := fun z => -z * bose z * (bose z + 1))
    (f'' := fun z => bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1))
  · intro z hz
    exact (hasDerivAt_canonicalQ (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (hasDerivAt_canonicalQ_deriv (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (canonicalQ_second_pos (by simpa using hz)).le

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

lemma canonicalExp_jensen (z₁ w₁ z₂ w₂ i j : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.exp (-(i * (a * z₁ + b * z₂) + j * (a * w₁ + b * w₂))) ≤
      a * Real.exp (-(i * z₁ + j * w₁)) + b * Real.exp (-(i * z₂ + j * w₂)) := by
  convert! convexOn_exp.2 (mem_univ (-(i*z₁+j*w₁)))
    (mem_univ (-(i*z₂+j*w₂))) ha hb hab using 1;
    simp only [smul_eq_mul]; congr 1; ring

lemma canonicalGroup_jensen (z₁ w₁ z₂ w₂ : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (n : ℕ) :
    canonicalGroup (a*z₁+b*z₂) (a*w₁+b*w₂) n ≤
      a * canonicalGroup z₁ w₁ n + b * canonicalGroup z₂ w₂ n := by
  unfold canonicalGroup
  have h₁ := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j _ =>
    canonicalExp_jensen z₁ w₁ z₂ w₂ (n+1 : ℕ) (j+1 : ℕ) ha hb hab)
  have h₂ := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    canonicalExp_jensen z₁ w₁ z₂ w₂ (i+1 : ℕ) (n+1 : ℕ) ha hb hab)
  have h := div_le_div_of_nonneg_right (add_le_add h₁ h₂)
    (show (0 : ℝ) ≤ (n+1 : ℕ) by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  convert! h using 1; ring

lemma normalizedEntropy_jensen {z₁ w₁ z₂ w₂ a b : ℝ}
    (hz₁ : 0 < z₁) (hw₁ : 0 < w₁) (hz₂ : 0 < z₂) (hw₂ : 0 < w₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    normalizedEntropy (a*z₁+b*z₂) (a*w₁+b*w₂) ≤
      a * normalizedEntropy z₁ w₁ + b * normalizedEntropy z₂ w₂ := by
  have hz : 0 < a*z₁+b*z₂ := by
    simpa only [mem_Ioi, smul_eq_mul] using (convex_Ioi (0 : ℝ)) hz₁ hz₂ ha hb hab
  have hw : 0 < a*w₁+b*w₂ := by
    simpa only [mem_Ioi, smul_eq_mul] using (convex_Ioi (0 : ℝ)) hw₁ hw₂ ha hb hab
  have hseries := hasSum_le (canonicalGroup_jensen z₁ w₁ z₂ w₂ ha hb hab)
    (hasSum_normalizedEntropy hz hw)
    (((hasSum_normalizedEntropy hz₁ hw₁).mul_left a).add
      ((hasSum_normalizedEntropy hz₂ hw₂).mul_left b))
  have hqz := convexOn_canonicalQ.2 hz₁ hz₂ ha hb hab
  have hqw := convexOn_canonicalQ.2 hw₁ hw₂ ha hb hab
  simp only [smul_eq_mul] at hqz hqw
  linarith

lemma hasDerivAt_normalizedEntropy_comp {z w : ℝ → ℝ} {t z' w' : ℝ}
    (hzD : HasDerivAt z z' t) (hwD : HasDerivAt w w' t)
    (hz : 0 < z t) (hw : 0 < w t) :
    HasDerivAt (fun s => normalizedEntropy (z s) (w s))
      (normalizedEntropyDz (z t) (w t) * z' + normalizedEntropyDz (w t) (z t) * w') t := by
  have hu := bose_pos hz
  have hv := bose_pos hw
  have huD := (hasDerivAt_bose hz).comp t hzD
  have hvD := (hasDerivAt_bose hw).comp t hwD
  have hnD := (huD.const_add 1).add hvD
  have h₁ := (Real.hasDerivAt_mul_log (by linarith : 1 + bose (z t) + bose (w t) ≠ 0)).comp t hnD
  have h₂ := (Real.hasDerivAt_mul_log (by linarith : bose (z t) + 1 ≠ 0)).comp t (huD.add_const 1)
  have h₃ := (Real.hasDerivAt_mul_log hu.ne').comp t huD
  have h₄ := (Real.hasDerivAt_mul_log (by linarith : bose (w t) + 1 ≠ 0)).comp t (hvD.add_const 1)
  have h₅ := (Real.hasDerivAt_mul_log hv.ne').comp t hvD
  convert! h₁.sub ((((h₂.add h₃).add h₄).add h₅).div_const 2) using 1
  unfold normalizedEntropyDz
  rw [show 1 + bose (w t) + bose (z t) = 1 + bose (z t) + bose (w t) by ring]
  ring

lemma positive_line {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : t ∈ Icc 0 1) :
    0 < x + t * (y - x) := by
  have h := (convex_Ioi (0 : ℝ)) hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  simp only [smul_eq_mul, mem_Ioi] at h
  nlinarith

lemma normalizedEntropy_tangent {z w Z W : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hZ : 0 < Z) (hW : 0 < W) :
    normalizedEntropy z w + normalizedEntropyDz z w * (Z-z) +
      normalizedEntropyDz w z * (W-w) ≤ normalizedEntropy Z W := by
  let f : ℝ → ℝ := fun t => normalizedEntropy (z+t*(Z-z)) (w+t*(W-w))
  have hc : ConvexOn ℝ (Icc 0 1) f := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := normalizedEntropy_jensen (positive_line hz hZ hx) (positive_line hw hW hx)
      (positive_line hz hZ hy) (positive_line hw hW hy) ha hb hab
    convert! h using 1; simp only [f, smul_eq_mul]
    congr 1 <;> nlinarith [congrArg (fun q : ℝ => q*z) hab, congrArg (fun q : ℝ => q*w) hab]
  have hd : HasDerivAt f (normalizedEntropyDz z w * (Z-z) +
      normalizedEntropyDz w z * (W-w)) 0 := by
    convert! hasDerivAt_normalizedEntropy_comp
      (((hasDerivAt_id (0 : ℝ)).mul_const (Z-z)).const_add z)
      (((hasDerivAt_id (0 : ℝ)).mul_const (W-w)).const_add w)
      (by simpa using hz) (by simpa using hw) using 1; simp
  have h := hc.le_slope_of_hasDerivAt (y := 1) (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, f, zero_mul, add_zero, one_mul, sub_zero, div_one] at h
  rw [show z+(Z-z)=Z by ring, show w+(W-w)=W by ring] at h
  linarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent := @_root_.OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent
