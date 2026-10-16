-- Prove2me | solution 1 for OAI.ShortEgyptian.prime_rpow_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:57:32.713983+00:00
-- url     : https://prove2.me/submissions/2ed32739-d5bc-404d-9c32-8d23bafbe40a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean:L71-L86
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prime_rpow_small. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_rpow_small {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1/2 ≤ σ) :
    0 < (p:ℝ)^(-σ) ∧ (p:ℝ)^(-σ) ≤ 3/4 := by
  have hpp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hp2 : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hs : 4/3 ≤ Real.sqrt (p:ℝ) := by
    apply (Real.le_sqrt (by norm_num) hpp.le).mpr
    norm_num
    linarith
  refine ⟨Real.rpow_pos_of_pos hpp _, ?_⟩
  calc
    _ ≤ (p:ℝ)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (Real.sqrt (p:ℝ))⁻¹ := by rw [Real.rpow_neg hpp.le, Real.sqrt_eq_rpow]
    _ ≤ 3/4 := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hpp)).mpr
      linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prime_rpow_small := @_root_.OAI.ShortEgyptian.prime_rpow_small
