-- Prove2me | solution 1 for OAI.ShortEgyptian.random_atom_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:48:30.927157+00:00
-- url     : https://prove2.me/submissions/1a92607a-9f9e-4a01-a674-809bb1327b97

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean:L82-L105
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_atom_bound. The node keeps its source
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

lemma random_atom_bound (S V P : ℝ) (s : ℕ) (hS : 2 ≤ S)
    (hP : S^99 ≤ P) (hsS : (s:ℝ) ≤ S) (hs : V/(140*Real.log S) ≤ (s:ℝ)) :
    (s:ℝ)^s/P^s ≤ Real.exp (-(7/10:ℝ)*V) := by
  have hSpos : 0 < S := by linarith
  have hL : 0 < Real.log S := Real.log_pos (by linarith)
  have hPpos : 0 < P := (pow_pos hSpos 99).trans_le hP
  have hratio : (s:ℝ)/P ≤ S/S^99 :=
    div_le_div₀ hSpos.le hsS (pow_pos hSpos 99) hP
  have heq : S/S^99 = Real.exp (-98*Real.log S) := by
    calc
      _ = Real.exp (Real.log S)/Real.exp (99*Real.log S) := by
        congr 1
        · exact (Real.exp_log hSpos).symm
        · rw [show (99:ℝ) = (99:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hSpos]
      _ = Real.exp (Real.log S-99*Real.log S) := (Real.exp_sub _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = ((s:ℝ)/P)^s := (div_pow _ _ _).symm
    _ ≤ (S/S^99)^s := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg s) hPpos.le) hratio s
    _ = Real.exp ((s:ℝ)*(-98*Real.log S)) := by rw [heq,Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ (by positivity : 0 < 140*Real.log S)).mp hs
      nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ShortEgyptian.random_atom_bound := @_root_.OAI.ShortEgyptian.random_atom_bound
