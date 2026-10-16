-- Prove2me | solution 1 for OAI.ShortEgyptian.prepare_denominator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:06:47.437439+00:00
-- url     : https://prove2.me/submissions/1be6a8bd-d5fd-44c1-ae0e-287eac9c2837

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean:L130-L149
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prepare_denominator. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_greedy_step
import Theorems.Thm_OAI_ShortEgyptian_prepare_aux
import Theorems.Thm_OAI_ShortEgyptian_prepared_cons

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma prepare_denominator (a b : ℕ) (ha : 0<a) (hab : a<b) (T : ℝ)
    (hT : 1<T) (hbT : (b:ℝ)<T) (k : ℕ)
    (hcap : T ≤ Real.exp ((2:ℝ)^k*Real.log 2)) : Prepared a b T (k+1) := by
  let z := quotient b a
  let r := residue b a z
  have hs := greedy_step a b ha hab
  change 2 ≤ z ∧ z ≤ b ∧ r < a ∧ _ at hs
  have hb : 0<b := ha.trans hab
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hz : 0<z := by omega
  have hr : r<b*z := by nlinarith [hs.2.2.1]
  have hsize : ((b*z:ℕ):ℝ)<T^2 := by
    push_cast
    have hh : (z:ℝ)≤b := by exact_mod_cast hs.2.1
    nlinarith
  have hsmall : (r:ℝ)/(b*z:ℕ) ≤ Real.exp (-Real.log 2) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),Nat.cast_mul]
    simpa only [one_div] using hs.2.2.2.2.2
  exact prepared_cons a b ha hab T k (prepare_aux k r (b*z) hr T (Real.log 2) hT
    (Real.log_pos (by norm_num)) hsize hsmall hcap)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prepare_denominator := @_root_.OAI.ShortEgyptian.prepare_denominator
