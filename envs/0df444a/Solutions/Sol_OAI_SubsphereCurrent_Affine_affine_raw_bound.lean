-- Prove2me | solution 1 for OAI.SubsphereCurrent.Affine.affine_raw_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:27:05.946862+00:00
-- url     : https://prove2.me/submissions/3f8a59eb-ed5b-4498-8488-6fa28c6f93c2

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/AffinePrecision.lean:L50-L124
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Affine.affine_raw_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

-- ---- from OAI.Probability.Subsphere.Estimates.AffinePrecision ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Affine
open scoped ENNReal NNReal

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,Real.log_inv] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

lemma log_thousand_lower : (4 : ℝ) ≤ Real.log 1000 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) (by norm_num : (256 : ℝ) ≤ 1000)
  rw [show (256 : ℝ) = 2^(8 : ℕ) by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [log_two_bounds.1]

lemma affine_parameters {d n ell : ℕ} (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) :
    let q := (n-1)/4
    2 ≤ q ∧ n ≤ 5*q ∧ d ≤ 2*n ∧ d/16 ≤ q ∧ d/8 ≤ 2*q ∧
      2*(d/32) ≤ 2*q ∧ ell*(d/16)/q+1 ≤ ell+1 := by
  dsimp
  have hq : 2 ≤ (n-1)/4 := by omega
  have hm : d/16 ≤ (n-1)/4 := by omega
  refine ⟨hq,by omega,by omega,hm,by omega,by omega,?_⟩
  have := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left ell hm)
  omega

lemma affine_raw_bound {d n ell J : ℕ} {η : ℝ}
    (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) (hell : 1 ≤ ell)
    (hJ : 1 ≤ J)
    (hbudget : Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
      ((32768 : ℝ)^n * (J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
        (ell*(d/16)/((n-1)/4)+1) ≤
      (16*((1000 : ℝ)^32)^ell*η)^(2*(d/32)) := by
  let q := (n-1)/4
  let a := 2*(d/32)
  let b := ell*(d/16)/q+1
  let c : ℝ := 16*((1000 : ℝ)^32)^ell
  obtain ⟨hq,hnq,hdn,_,hpq,haq,hb⟩ := affine_parameters hd hn
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnr : (n : ℝ) ≤ 5*q := by exact_mod_cast hnq
  have hdr : (d : ℝ) ≤ 2*n := by exact_mod_cast hdn
  have hpr : ((d/8 : ℕ) : ℝ) ≤ 2*q := by exact_mod_cast hpq
  have hbr : (b : ℝ) ≤ ell+1 := by exact_mod_cast hb
  have her : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have har : (a : ℝ) ≤ 2*q := by exact_mod_cast haq
  have hcp : 0 < c := by dsimp [c]; positivity
  have hlogη : Real.log η ≤ -Real.log c := by
    have hl := Real.log_le_log (mul_pos hcp hη) hsmall
    rw [Real.log_mul hcp.ne' hη.ne',Real.log_one] at hl
    linarith
  have hMQ : Real.log (J : ℝ)/q ≤ 2*d := by
    apply (div_le_iff₀ hqp).2
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.2
      (show 0 ≤ ((d/8 : ℕ) : ℝ)*d by positivity)
    have hh' := mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg d)
    nlinarith
  have hlog32 : Real.log (32768 : ℝ) ≤ 15 := by
    rw [show (32768 : ℝ) = 2^(15 : ℕ) by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  have hi : (n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q ≤ 19*n := by
    have := mul_le_mul_of_nonneg_left hlog32 (Nat.cast_nonneg n)
    linarith
  have hfull : (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 38*n*ell := by
    calc
      _ ≤ (b : ℝ)*(19*n) := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg b)
      _ ≤ ((ell : ℝ)+1)*(19*n) := mul_le_mul_of_nonneg_right hbr (by positivity)
      _ ≤ 38*n*ell := by nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) (sub_nonneg.mpr her)]
  have hlogc : 128*(ell : ℝ) ≤ Real.log c := by
    dsimp [c]
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    have := mul_le_mul_of_nonneg_left log_thousand_lower (show 0 ≤ (ell : ℝ)*32 by positivity)
    have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hcost : Real.log 3 + (n : ℝ)*Real.log 4 +
      (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 2*q*Real.log c := by
    have h3 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    have h4 := mul_le_mul_of_nonneg_left (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4))
      (Nat.cast_nonneg n)
    have hqc := mul_le_mul_of_nonneg_left hlogc (show (0 : ℝ) ≤ 2*q by positivity)
    have hnell := mul_le_mul_of_nonneg_right hnr (Nat.cast_nonneg ell)
    have hne : (n : ℝ) ≤ n*ell := by nlinarith
    nlinarith
  have hηcost := mul_le_mul_of_nonneg_left hlogη (sub_nonneg.mpr har)
  apply (Real.log_le_log_iff (by positivity) (by positivity : 0 < (c*η)^a)).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_rpow hJp,
    Real.log_pow,Real.log_mul hcp.ne' hη.ne']
  change Real.log 3 + (n : ℝ)*Real.log 4 + ((2*q : ℕ) : ℝ)*Real.log η +
    (b : ℝ)*((n : ℝ)*Real.log 32768 + (1/(q : ℝ))*Real.log (J : ℝ)) ≤
      (a : ℝ)*(Real.log c+Real.log η)
  rw [show (1/(q : ℝ))*Real.log (J : ℝ) = Real.log (J : ℝ)/q by ring]
  push_cast
  nlinarith

end SubsphereCurrent.Affine
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Affine
open scoped ENNReal NNReal


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Affine.affine_raw_bound := @_root_.OAI.SubsphereCurrent.Affine.affine_raw_bound
