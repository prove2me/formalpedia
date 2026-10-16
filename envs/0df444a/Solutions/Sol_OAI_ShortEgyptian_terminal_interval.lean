-- Prove2me | solution 1 for OAI.ShortEgyptian.terminal_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:27:29.503316+00:00
-- url     : https://prove2.me/submissions/0ae8952d-e691-4b32-a1fe-b558ac2acc71

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean:L36-L50
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.terminal_interval. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uA

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma terminal_interval (S : ℝ) (h : ListScale S) (u : ℕ)
    (hu : u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊) :
    3 ≤ u ∧ 100000*Real.log S ≤ Real.log u ∧ Real.log u ≤ (scaleM S:ℝ) := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
  have huR : S^100000 < (u:ℝ) := Nat.lt_of_floor_lt (by omega)
  have hpow : S ≤ S^100000 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [h.two_le] : (1:ℝ)≤S) (by norm_num : 1 ≤ 100000)
  have hu2 : (2:ℝ) < u := h.two_le.trans hpow |>.trans_lt huR
  have huN : 3 ≤ u := by exact_mod_cast (show (2:ℝ)<u from hu2)
  have hu0 : 0 < (u:ℝ) := by linarith
  refine ⟨huN,?_,(Real.log_le_iff_le_exp hu0).mpr ((Nat.cast_le.mpr hhi).trans (Nat.floor_le (Real.exp_nonneg _)))⟩
  have hh := Real.log_le_log (pow_pos h.S_pos 100000) huR.le
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.terminal_interval := @_root_.OAI.ShortEgyptian.terminal_interval
