-- Prove2me | solution 1 for OAI.ShortEgyptian.random_fresh_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:47:01.551929+00:00
-- url     : https://prove2.me/submissions/2b76f953-2530-4932-be35-00eddb7c2cdf

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean:L55-L80
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_fresh_bound. The node keeps its source
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

lemma random_fresh_bound {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (S V : ℝ) (hS : 2 ≤ S) (hV : 0 < V)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100)
    (hs : (Fintype.card J:ℝ) ≤ 3*V/(400*Real.log S)) (f : J → A) :
    (∏ j,p (f j):ℕ) < Real.exp (4/5*V) := by
  have hSpos : 0 < S := by linarith
  have hL : 0 < Real.log S := Real.log_pos (by linarith)
  have hmax' (a : A) : (p a:ℝ) ≤ S^101 := by
    calc
      _ ≤ 2*S^100 := hmax a
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by ring
  have hprod : ((∏ j,p (f j):ℕ):ℝ) ≤ (S^101)^Fintype.card J := by
    push_cast
    calc
      _ ≤ ∏ _j : J, S^101 := prod_le_prod (fun _ _ => by positivity) (fun j _ => hmax' (f j))
      _ = _ := by simp
  have hExp : (S^101)^Fintype.card J = Real.exp ((Fintype.card J:ℝ)*101*Real.log S) := by
    calc
      _ = Real.exp (Real.log ((S^101)^Fintype.card J)) := (Real.exp_log (by positivity)).symm
      _ = _ := by rw [Real.log_pow,Real.log_pow]; congr 1; ring
  apply hprod.trans_lt
  rw [hExp]
  apply Real.exp_lt_exp.mpr
  have hh := (le_div_iff₀ (by positivity : 0 < 400*Real.log S)).mp hs
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.random_fresh_bound.{uJ,uA} := @_root_.OAI.ShortEgyptian.random_fresh_bound.{uJ,uA}
