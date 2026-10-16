-- Prove2me | solution 1 for OAI.ShortEgyptian.eventually_density_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:58:31.519217+00:00
-- url     : https://prove2.me/submissions/24ff3427-a1b6-48e2-837f-9893ff1912ba

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DensityBounds.lean:L73-L106
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.eventually_density_numeric. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Theorems.Thm_OAI_ShortEgyptian_depth_bound
import Theorems.Thm_OAI_ShortEgyptian_eventually_log_pow_le
import Theorems.Thm_OAI_ShortEgyptian_eventually_scaleM_large

-- ---- from OAI.NumberTheory.ShortEgyptian.ParameterBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocalConstant_pos (r : ℕ) : 0 < reciprocalConstantNat r := by
  unfold reciprocalConstantNat
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma eventually_depth_tail :
    ∀ᶠ S : ℝ in atTop,
      (depth S:ℝ)*Real.exp (-(1/250:ℝ)*scaleM S) < 1/2 := by
  let K : ℝ := 3*(dimX:ℝ)*10000
  have hK : 0 < K := by norm_num [K,dimX,dimM]
  filter_upwards [eventually_scaleM_large 500,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_pow_le 4 1 (by norm_num : (0:ℝ)<1),eventually_ge_atTop (4*K),
    eventually_gt_atTop (0:ℝ)] with S hm hL hbig hSK hS
  rw [Real.rpow_one,pow_one] at hbig
  have hb : 4*Real.log S ≤ S := by linarith
  have hmb := scaleM_bounds S hL hb
  have hd := depth_bound S hS hL hmb.1 hmb.2.2
  have hE : Real.exp (-(1/250:ℝ)*scaleM S) ≤ 1/S^2 := by
    calc
      _ ≤ Real.exp (-(2*Real.log S)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log hS]; simp [pow_two]
  have hLS : Real.log S ≤ S := by have hh := Real.log_le_sub_one_of_pos hS; linarith
  calc
    _ ≤ (K*S)*(1/S^2) := mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left hLS hK.le)) hE
      (Real.exp_nonneg _) (by positivity)
    _ = K/S := by field_simp
    _ ≤ 1/4 := (div_le_iff₀ hS).mpr (by linarith)
    _ < _ := by norm_num

lemma eventually_ListScale : ∀ᶠ S : ℝ in atTop, ListScale S := by
  let A : ℝ := (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC)
  have hA : 0 < A := mul_pos (by exact_mod_cast reciprocalConstant_pos (3*dimC)) (by positivity)
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 100,
    eventually_log_pow_le 100001 1 (by norm_num : (0:ℝ)<1),eventually_scaleM_large 1000000,
    Real.tendsto_log_atTop.eventually_ge_atTop (reciprocalPower (3*dimC):ℝ),
    eventually_ge_atTop (4*Real.log A),eventually_depth_tail]
    with S hS hlog hbig hm hP hA' hd
  rw [Real.rpow_one,pow_one] at hbig
  refine ⟨hS,hlog,by linarith,hm,hP,?_,hd⟩
  exact (Real.log_le_iff_le_exp hA).mp (by linarith)

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DensityBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Filter Topology

lemma eventually_density_numeric : ∀ᶠ S : ℝ in atTop,
    (depth S:ℝ)*Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/8 := by
  let B : ℝ := 1000*(2*(descentR:ℝ)+2)
  let K : ℝ := 3*(dimX:ℝ)*10000
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; norm_num [dimX,dimM]
  filter_upwards [eventually_ListScale,eventually_log_pow_le (2*B) 1 (by norm_num : (0:ℝ)<1/2),
    eventually_log_pow_le 1 1 (by norm_num : (0:ℝ)<1/4),eventually_ge_atTop (8*K)] with S h hnum hlog hS
  simp only [pow_one,one_mul] at hnum hlog
  have hp : 0 < S^(1/2:ℝ) := Real.rpow_pos_of_pos h.S_pos _
  have hlo : 0 < Real.log S := by linarith [h.log_one]
  have heq : S^(1/2:ℝ)*S^(1/2:ℝ)=S := by rw [←Real.rpow_add h.S_pos]; norm_num
  have hm : B*S^(1/2:ℝ) ≤ (scaleM S:ℝ) := by
    apply le_trans _ h.m_bounds.1
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mpr
    have hh := mul_le_mul_of_nonneg_right hnum hp.le
    rw [heq] at hh
    nlinarith [mul_nonneg hB.le hp.le]
  have heq' : S^(1/2:ℝ)*S^(-(1/4:ℝ))=S^(1/4:ℝ) := by rw [←Real.rpow_add h.S_pos]; norm_num
  have hmm := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg h.S_pos.le (-(1/4:ℝ)))
  rw [mul_assoc,heq'] at hmm
  have hneg : 2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ)) ≤ -(2*Real.log S) := by
    dsimp [B] at hmm
    nlinarith
  have hE : Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/S^2 := by
    calc
      _ ≤ Real.exp (-(2*Real.log S)) := Real.exp_le_exp.mpr hneg
      _ = _ := by rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log h.S_pos]; simp [pow_two]
  have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
  have hLS : Real.log S ≤ S := by linarith [Real.log_le_sub_one_of_pos h.S_pos]
  calc
    _ ≤ (K*S)*(1/S^2) := mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left hLS hK.le)) hE (Real.exp_nonneg _) (mul_nonneg hK.le h.S_pos.le)
    _ = K/S := by field_simp
    _ ≤ _ := (div_le_iff₀ h.S_pos).mpr (by linarith)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Filter Topology


theorem solution : type_of% @_root_.OAI.ShortEgyptian.eventually_density_numeric := @_root_.OAI.ShortEgyptian.eventually_density_numeric
