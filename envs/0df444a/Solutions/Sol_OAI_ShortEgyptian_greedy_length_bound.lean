-- Prove2me | solution 1 for OAI.ShortEgyptian.greedy_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:08:50.550989+00:00
-- url     : https://prove2.me/submissions/9beac118-4db2-4a89-8449-e40e3e7edaee

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean:L173-L201
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.greedy_length_bound. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma greedy_length_bound (S : ℝ) (hS : 1≤S) (hlog : 1≤Real.log S) :
    ((greedySteps S+1:ℕ):ℝ) ≤ greedyConstant*Real.log S := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h₂' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hD : (1:ℝ)≤dimC := by norm_num [dimC,dimX,dimM]
  have hSp : 0<S := lt_of_lt_of_le (by norm_num) hS
  have hD' : 0<(dimC:ℝ) := by linarith
  have hx : 1≤(dimC:ℝ)/Real.log 2 := (le_div_iff₀ h₂).mpr (by nlinarith)
  have hprod : 1≤(dimC:ℝ)*S/Real.log 2 := by
    rw [mul_div_right_comm]
    nlinarith
  have ht : 0 ≤ Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2 :=
    div_nonneg (Real.log_nonneg hprod) h₂.le
  have hh := Nat.ceil_lt_add_one ht
  change (greedySteps S:ℝ) < Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2+1 at hh
  have heq : Real.log ((dimC:ℝ)*S/Real.log 2) = Real.log ((dimC:ℝ)/Real.log 2)+Real.log S := by
    rw [mul_div_right_comm,Real.log_mul (div_pos hD' h₂).ne' hSp.ne']
  have hL : Real.log ((dimC:ℝ)/Real.log 2) ≤ (dimC:ℝ)/Real.log 2 :=
    (Real.log_le_sub_one_of_pos (div_pos hD' h₂)).trans (by linarith)
  have hcoef : 0 ≤ (dimC:ℝ)/(Real.log 2)^2+2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hlog hcoef
  have hd := div_le_div_of_nonneg_right hL h₂.le
  rw [heq,add_div] at hh
  dsimp [greedyConstant]
  push_cast
  have heq' : (dimC:ℝ)/(Real.log 2)/Real.log 2 = (dimC:ℝ)/(Real.log 2)^2 := by ring
  rw [heq'] at hd
  simp only [div_eq_mul_inv] at hh hb hd ⊢
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq


theorem solution : type_of% @_root_.OAI.ShortEgyptian.greedy_length_bound := @_root_.OAI.ShortEgyptian.greedy_length_bound
