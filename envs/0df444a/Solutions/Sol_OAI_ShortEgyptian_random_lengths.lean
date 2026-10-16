-- Prove2me | solution 1 for OAI.ShortEgyptian.random_lengths
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:45:11.75039+00:00
-- url     : https://prove2.me/submissions/97e00eb8-4402-47b5-af0d-bfef37914511

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean:L13-L53
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_lengths. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.RandomBounds ----
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_lengths (S V : ℝ) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (hV : 100000*Real.log S ≤ V) (hVS : V ≤ S) :
    let m := ⌊S/Real.log S⌋₊
    let s := ⌊3*V/(400*Real.log S)⌋₊
    S/(2*Real.log S) ≤ (m:ℝ) ∧ (m:ℝ) ≤ S ∧
      V/(140*Real.log S) ≤ (s:ℝ) ∧ (s:ℝ) ≤ 3*V/(400*Real.log S) ∧
      8*s ≤ m ∧ (s:ℝ) ≤ S ∧ 100 ≤ min (m:ℝ) V := by
  have hL : 0 < Real.log S := by linarith
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by linarith
  dsimp only
  have hmU := Nat.floor_le (div_nonneg hSpos.le hL.le)
  have hmL := Nat.sub_one_lt_floor (S/Real.log S)
  have hsU := Nat.floor_le (div_nonneg (by positivity : 0 ≤ 3*V) (by positivity : 0 ≤ 400*Real.log S))
  have hsL := Nat.sub_one_lt_floor (3*V/(400*Real.log S))
  have h200 : 200 ≤ S/Real.log S := (le_div_iff₀ hL).mpr hS
  have hm : S/(2*Real.log S) ≤ (⌊S/Real.log S⌋₊:ℝ) := by
    have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
    rw [heq]
    linarith
  have hs : V/(140*Real.log S) ≤ (⌊3*V/(400*Real.log S)⌋₊:ℝ) := by
    have hr : 100000 ≤ V/Real.log S := (le_div_iff₀ hL).mpr hV
    have heq : 3*V/(400*Real.log S) = (3/400)*(V/Real.log S) := by ring
    have heq' : V/(140*Real.log S) = (1/140)*(V/Real.log S) := by ring
    nth_rw 1 [heq] at hsL
    rw [heq']
    linarith
  have hmS : (⌊S/Real.log S⌋₊:ℝ) ≤ S := hmU.trans ((div_le_self hSpos.le hlog))
  have h8 : 8*(⌊3*V/(400*Real.log S)⌋₊:ℝ) ≤ (⌊S/Real.log S⌋₊:ℝ) := by
    have hh : 8*(3*V/(400*Real.log S)) ≤ S/(2*Real.log S) := by
      rw [←mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0 < 400*Real.log S) (by positivity : 0 < 2*Real.log S)).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hsU (by norm_num)).trans (hh.trans hm)
  refine ⟨hm,hmS,hs,hsU,by exact_mod_cast h8,?_,?_⟩
  · linarith
  · apply le_min
    · have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
      rw [heq] at hm
      linarith
    · linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ShortEgyptian.random_lengths := @_root_.OAI.ShortEgyptian.random_lengths
