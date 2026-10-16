-- Prove2me | solution 1 for OAI.ShortEgyptian.level_fraction_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:46:13.467491+00:00
-- url     : https://prove2.me/submissions/ea5f4296-1609-4f0c-a9dc-c6afb65bf82e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean:L62-L79
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.level_fraction_lt. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma scaleRho_le_one (S : ℝ) : scaleRho S ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have hh : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _; nlinarith)

lemma level_succ (S : ℝ) (j : ℕ) : level S (j+1) = level S j*scaleRho S := by
  unfold level scaleRho
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring

lemma level_antitone (S : ℝ) : Antitone (level S) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [level_succ]
  exact mul_le_of_le_one_right (level_pos S j).le (scaleRho_le_one S)

lemma level_zero (S : ℝ) : level S 0 = Real.exp ((dimX:ℝ)*S) := by simp [level]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DescentSets ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma level_fraction_lt (S : ℝ) (h : ListScale S) (C M j u : ℕ)
    (hM : Real.exp S < (M:ℝ)) (hC : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hu : (u:ℝ) ≤ level S j) : u < M*levelMultiplier S C j := by
  have hm : 1 ≤ M := by
    have hp : (0:ℝ)<M := (Real.exp_pos S).trans hM
    exact_mod_cast (show (1:ℕ)≤M by exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hp.ne'))
  unfold levelMultiplier
  split_ifs with hx
  · have hu' : (u:ℝ)<C := by
      apply hu.trans_lt
      apply (level_antitone S (Nat.zero_le j)).trans_lt
      rw [level_zero]
      apply (Real.exp_lt_exp.mpr ?_).trans_le hC
      have hd : (dimX:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
      exact mul_lt_mul_of_pos_right hd h.S_pos
    exact (by exact_mod_cast hu' : u < C).trans_le (Nat.le_mul_of_pos_left _ hm)
  · simp only [mul_one]
    exact_mod_cast hu.trans_lt ((le_of_not_gt hx).trans_lt hM)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.level_fraction_lt := @_root_.OAI.ShortEgyptian.level_fraction_lt
