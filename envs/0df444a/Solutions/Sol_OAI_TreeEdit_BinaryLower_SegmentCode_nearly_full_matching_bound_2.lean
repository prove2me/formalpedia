-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.SegmentCode.nearly_full_matching_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:51:36.752477+00:00
-- url     : https://prove2.me/submissions/c2e6144a-1962-4bde-81b7-30a3e53b536f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentCodeEstimates.lean:L49-L81
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.SegmentCode.nearly_full_matching_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentCodeEstimates ----
namespace OAI

namespace TreeEdit.BinaryLower
namespace SegmentCode

open Finset

/-- A weighted binomial coefficient estimate used for random binary blocks. -/
theorem choose_weighted_le (a u : ℕ) (hu : u ≤ a) :
    (a.choose u : ℝ) * 4 ^ (a-u) ≤ 5 ^ a := by
  have h := Finset.single_le_sum
    (f := fun i : ℕ => (1 : ℝ)^i * 4^(a-i) * (a.choose i : ℝ))
    (fun i hi => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))
  have hsum := add_pow (1 : ℝ) 4 a
  norm_num only [one_pow, one_mul, show (1 : ℝ) + 4 = 5 by norm_num] at hsum h
  rw [← hsum] at h
  simpa [mul_comm] using h

/-- A convenient division-free consequence of the weighted estimate. -/
theorem choose_le_weighted (a u : ℕ) (hu : u ≤ a) :
    (a.choose u : ℝ) ≤ (5/4 : ℝ)^a * 4^u := by
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < 4^a by positivity)).mp
  calc
    (a.choose u : ℝ) * 4^a = ((a.choose u : ℝ) * 4^(a-u)) * 4^u := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hu]
    _ ≤ 5^a * 4^u := mul_le_mul_of_nonneg_right (choose_weighted_le a u hu) (by positivity)
    _ = ((5/4 : ℝ)^a * 4^u) * 4^a := by
      rw [div_pow]
      field_simp

private theorem weighted_identity (s u : ℕ) :
    (((5/4 : ℝ)^(s+u) * 4^u)^2) * (1/2 : ℝ)^s =
      (25/32 : ℝ)^(s+u) * 32^u := by
  simp only [pow_add, mul_pow, ← pow_mul]
  rw [Nat.mul_comm s 2, Nat.mul_comm u 2]
  simp only [pow_mul]
  calc
    ((5/4 : ℝ)^2)^s * ((5/4 : ℝ)^2)^u * ((4 : ℝ)^2)^u * (1/2 : ℝ)^s =
        ((5/4 : ℝ)^2 * (1/2 : ℝ))^s * ((5/4 : ℝ)^2 * (4 : ℝ)^2)^u := by
      simp only [mul_pow]
      ring
    _ = (25/32 : ℝ)^s * (25 : ℝ)^u := by norm_num
    _ = (25/32 : ℝ)^s * (25/32 : ℝ)^u * (32 : ℝ)^u := by
      rw [mul_assoc, ← mul_pow]
      norm_num

/-- A prescribed almost-full common subsequence has an exponentially small union bound.
The estimate is deliberately weaker than the manuscript's `2^(-a/2)` but sufficient
for the same fixed-length conversion theorem. -/
theorem nearly_full_matching_bound (a s : ℕ) (hs : s ≤ a)
    (hlarge : 99*a ≤ 100*s) :
    (a.choose s : ℝ)^2 * (1/2 : ℝ)^s ≤ (9/10 : ℝ)^a := by
  let u := a-s
  have hu : u ≤ a := Nat.sub_le a s
  have hsum : s+u = a := Nat.add_sub_of_le hs
  have hsmall : 100*u ≤ a := by dsimp [u]; omega
  have hchoose : (a.choose s : ℝ) ≤ (5/4 : ℝ)^a * 4^u := by
    simpa only [u, Nat.choose_symm hs] using choose_le_weighted a u hu
  have hraw : (a.choose s : ℝ)^2 * (1/2 : ℝ)^s ≤
      (25/32 : ℝ)^a * 32^u := by
    calc
      _ ≤ ((5/4 : ℝ)^a * 4^u)^2 * (1/2 : ℝ)^s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hchoose 2)
          (by positivity)
      _ = _ := by rw [← hsum]; exact weighted_identity s u
  have h100 : ((25/32 : ℝ)^a * 32^u)^100 ≤ ((9/10 : ℝ)^a)^100 := by
    calc
      _ = ((25/32 : ℝ)^100)^a * (32 : ℝ)^(100*u) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a 100,
          Nat.mul_comm u 100, pow_mul]
      _ ≤ ((25/32 : ℝ)^100)^a * (32 : ℝ)^a :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hsmall)
          (by positivity)
      _ = (((25/32 : ℝ)^100) * 32)^a := (mul_pow _ _ _).symm
      _ ≤ ((9/10 : ℝ)^100)^a :=
        pow_le_pow_left₀ (by positivity) (by norm_num) a
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 100 a]
  apply le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
  exact (pow_le_pow_left₀ (by positivity) hraw 100).trans h100

end SegmentCode
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.nearly_full_matching_bound := @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.nearly_full_matching_bound
