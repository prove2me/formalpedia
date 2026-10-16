-- Prove2me | solution 1 for OAI.ShortEgyptian.products_scale_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:15:17.251192+00:00
-- url     : https://prove2.me/submissions/3e632c51-391e-4bb6-976e-3a03a4d55176

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean:L82-L98
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.products_scale_bound. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.ListConstruction ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma products_scale_bound {J : Type uJ} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (a : J → ℕ) (ha : ∀ j, (a j:ℝ) ≤ 2*S^100) :
    ((∏ j,a j : ℕ):ℝ) ≤ Real.exp (101*S) := by
  have hS0 : 0 < S := by linarith
  have hamp (j : J) : (a j:ℝ) ≤ Real.exp (101*Real.log S) := by
    calc
      _ ≤ 2*S^100 := ha j
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = S^101 := by ring
      _ = Real.exp (101*Real.log S) := by rw [←Real.exp_log (pow_pos hS0 101),Real.log_pow]; norm_num
  push_cast
  calc
    _ ≤ ∏ _j : J, Real.exp (101*Real.log S) := prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hamp j)
    _ = Real.exp ((Fintype.card J:ℝ)*(101*Real.log S)) := by simp only [prod_const,card_univ,Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by have hh := (le_div_iff₀ hlog).mp hm; nlinarith)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uJ} : type_of% @_root_.OAI.ShortEgyptian.products_scale_bound.{uJ} := @_root_.OAI.ShortEgyptian.products_scale_bound.{uJ}
