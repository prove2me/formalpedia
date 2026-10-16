-- Prove2me | solution 1 for OAI.ShortEgyptian.mean_square_correlation_exp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:43:31.167279+00:00
-- url     : https://prove2.me/submissions/f0600e38-88b0-43ea-a48a-3ebcc91ad13a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean:L153-L172
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.mean_square_correlation_exp. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_mean_square_correlation_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.ProductCorrelations ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma mean_square_correlation_exp {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (hk : 4*k ≤ Fintype.card J) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      Real.exp (-(Fintype.card J:ℝ)/16)+epsilon := by
  have hbound : (2:ℝ)^k*(3/4:ℝ)^Fintype.card J ≤ Real.exp (-(Fintype.card J:ℝ)/16) := by
    have hL : Real.log (3/4:ℝ) ≤ -(1/4:ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/4)
      linarith
    have h2 : Real.log (2:ℝ) ≤ 3/4 := by linarith [Real.log_two_lt_d9]
    have hkR : 4*(k:ℝ) ≤ Fintype.card J := by exact_mod_cast hk
    rw [← Real.exp_log (by positivity : (0:ℝ)<(2:ℝ)^k*(3/4:ℝ)^Fintype.card J)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    have h1 := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (Fintype.card J))
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
    nlinarith only [h1,h3,hkR]
  exact (mean_square_correlation_bound F hnorm k epsilon heps hcorr).trans (add_le_add hbound le_rfl)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.mean_square_correlation_exp.{uJ,uA} := @_root_.OAI.ShortEgyptian.mean_square_correlation_exp.{uJ,uA}
