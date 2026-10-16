-- Prove2me | solution 1 for OAI.ShortEgyptian.greedy_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:00:32.254105+00:00
-- url     : https://prove2.me/submissions/cb3576d3-2527-45ad-bdba-b27b0e1b6d56

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean:L9-L55
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.greedy_step. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma greedy_step (A C : ℕ) (hA : 0 < A) (hAC : A < C) :
    let z := quotient C A
    let r := residue C A z
    2 ≤ z ∧ z ≤ C ∧ r < A ∧
      (A:ℚ)/C = 1/(z:ℚ)+(r:ℚ)/(C*z) ∧
      (r:ℝ)/(C*z) ≤ ((A:ℝ)/C)^2 ∧ (r:ℝ)/(C*z) ≤ 1/2 := by
  dsimp
  let z := quotient C A
  let r := residue C A z
  change 2 ≤ z ∧ z ≤ C ∧ r < A ∧
    (A:ℚ)/C = 1/(z:ℚ)+(r:ℚ)/(C*z) ∧
      (r:ℝ)/(C*z) ≤ ((A:ℝ)/C)^2 ∧ (r:ℝ)/(C*z) ≤ 1/2
  have hC : 0 < C := hA.trans hAC
  have hz := quotient_spec hC hA
  have hr := residue_spec hC hA
  change 0 < z ∧ C ≤ A*z ∧ A*z < C+A at hz
  change r < A ∧ C+r=A*z at hr
  have hz2 : 2 ≤ z := by nlinarith
  have hzC : z ≤ C := by
    change ⌈(C:ℚ)/(A:ℚ)⌉₊ ≤ C
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast hA : (0:ℚ)<A)).mpr
    have ha1 : (1:ℚ) ≤ A := by exact_mod_cast hA
    nlinarith [show (0:ℚ)≤C by positivity]
  have hCq : (C:ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hzq : (z:ℚ) ≠ 0 := by exact_mod_cast hz.1.ne'
  have hCr : (0:ℝ)<C := by exact_mod_cast hC
  have hzr : (0:ℝ)<z := by exact_mod_cast hz.1
  have har : (0:ℝ)<A := by exact_mod_cast hA
  have hrR : (r:ℝ) < A := by exact_mod_cast hr.1
  have hACR : (A:ℝ)<C := by exact_mod_cast hAC
  have hzr2 : (2:ℝ)≤z := by exact_mod_cast hz2
  have hvR : (C:ℝ)≤A*z := by exact_mod_cast hz.2.1
  refine ⟨hz2,hzC,hr.1,?_,?_,?_⟩
  · have hre : (C:ℚ)+r=A*z := by exact_mod_cast hr.2
    field_simp
    nlinarith
  · have h1 : 1/(z:ℝ) ≤ (A:ℝ)/C := by
      apply (div_le_div_iff₀ hzr hCr).mpr
      simpa using hvR
    calc
      (r:ℝ)/(C*z) ≤ (A:ℝ)/(C*z) := div_le_div_of_nonneg_right hrR.le (mul_nonneg hCr.le hzr.le)
      _ = ((A:ℝ)/C)*(1/(z:ℝ)) := by ring
      _ ≤ ((A:ℝ)/C)*((A:ℝ)/C) := mul_le_mul_of_nonneg_left h1 (div_nonneg har.le hCr.le)
      _ = _ := by ring
  · apply (div_le_iff₀ (mul_pos hCr hzr)).mpr
    nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq


theorem solution : type_of% @_root_.OAI.ShortEgyptian.greedy_step := @_root_.OAI.ShortEgyptian.greedy_step
