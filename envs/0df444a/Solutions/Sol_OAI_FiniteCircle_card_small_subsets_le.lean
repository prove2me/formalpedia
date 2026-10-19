-- Prove2me | solution 1 for OAI.FiniteCircle.card_small_subsets_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:37:43.66659+00:00
-- url     : https://prove2.me/submissions/239d1300-0f28-4f98-a07c-f4a3858ab109

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BitCounting.lean:L117-L151
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.card_small_subsets_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery

-- ---- from OAI.Combinatorics.FiniteCircle.BitCounting ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem card_small_subsets_le (w : ℕ) :
    ((Finset.univ.filter (fun S : Finset (Fin w) => (S.card : ℝ) ≤ (w : ℝ)/1048576)).card : ℝ) ≤
      Real.exp ((w : ℝ)/512) := by
  classical
  let K := Finset.univ.filter (fun S : Finset (Fin w) => (S.card : ℝ) ≤ (w : ℝ)/1048576)
  let z : ℝ := 1/1024
  have hz : 0 < z := by norm_num [z]
  have hlog : -1024 ≤ Real.log z := by
    have h := Real.log_le_sub_one_of_pos (x := 1024) (by norm_num)
    simp only [z, one_div, Real.log_inv]
    linarith
  have hlow (S : Finset (Fin w)) (hS : S ∈ K) : Real.exp (-(w : ℝ)/1024) ≤ z^S.card := by
    have hs := (Finset.mem_filter.mp hS).2
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg S.card)
    have he : -(w : ℝ)/1024 ≤ (S.card : ℝ)*Real.log z := by nlinarith
    have h := Real.exp_le_exp.mpr he
    simpa only [Real.exp_nat_mul, Real.exp_log hz] using h
  have htotal : ∑ S : Finset (Fin w), z^S.card = (z+1)^w := by
    simpa using Finset.sum_pow_mul_eq_add_pow z (1 : ℝ) (Finset.univ : Finset (Fin w))
  have hsum : (K.card : ℝ) * Real.exp (-(w : ℝ)/1024) ≤ (z+1)^w := calc
    _ = ∑ _S ∈ K, Real.exp (-(w : ℝ)/1024) := by simp
    _ ≤ ∑ S ∈ K, z^S.card := Finset.sum_le_sum hlow
    _ ≤ ∑ S : Finset (Fin w), z^S.card := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => pow_nonneg hz.le _)
    _ = _ := htotal
  have hupper : (z+1)^w ≤ Real.exp ((w : ℝ)/1024) := by
    have hl := Real.log_le_sub_one_of_pos (x := z+1) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg w)
    have hh : (w : ℝ)*Real.log (z+1) ≤ (w : ℝ)/1024 := by dsimp [z] at *; nlinarith
    have hh := Real.exp_le_exp.mpr hh
    simpa only [Real.exp_nat_mul, Real.exp_log (show 0 < z+1 by positivity)] using hh
  calc
    (K.card : ℝ) ≤ (z+1)^w / Real.exp (-(w : ℝ)/1024) := (le_div_iff₀ (Real.exp_pos _)).mpr hsum
    _ ≤ Real.exp ((w : ℝ)/1024) / Real.exp (-(w : ℝ)/1024) := div_le_div_of_nonneg_right hupper (Real.exp_pos _).le
    _ = Real.exp ((w : ℝ)/512) := by rw [← Real.exp_sub]; congr 1; ring

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.card_small_subsets_le := @_root_.OAI.FiniteCircle.card_small_subsets_le
