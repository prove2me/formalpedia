-- Prove2me | solution 1 for OAI.ShortEgyptian.random_pair_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:52:01.748003+00:00
-- url     : https://prove2.me/submissions/9b9f0bad-da79-4bea-abe7-d130f07e5b34

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean:L184-L200
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_pair_scalar. The node keeps its source
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

lemma random_pair_scalar (u : ℕ) (hV : 40 ≤ Real.log u) :
    Real.exp 1/(Real.exp (Real.log u/10))^(3/4:ℝ)+
      Real.sqrt u*Real.exp (-(7/10:ℝ)*Real.log u) ≤
      Real.exp (-(1/20:ℝ)*Real.log u)+Real.exp (-(1/5:ℝ)*Real.log u) := by
  have huR : 0 < (u:ℝ) := by
    contrapose! hV
    have hh : u = 0 := by exact_mod_cast (le_antisymm hV (Nat.cast_nonneg u))
    simp [hh]
  apply add_le_add
  · rw [←Real.exp_mul,←Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos huR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    ring_nf
    rfl

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ShortEgyptian.random_pair_scalar := @_root_.OAI.ShortEgyptian.random_pair_scalar
