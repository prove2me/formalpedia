-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_pow_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:15:50.074989+00:00
-- url     : https://prove2.me/submissions/f24d8423-9be8-4228-a341-5b3fdfeae155

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open Filter Finset
open scoped Topology
theorem h49_pi_pow_lower (e C : ℕ) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → C * k ^ e ≤ Nat.primeCounting (k ^ (e + 1)) := by
  let A : ℕ := (e+1)*(C+2)
  refine ⟨16*A^2 + 2, fun k hk => ?_⟩
  have hk2 : 2 ≤ k := by omega
  set x : ℝ := (k:ℝ) with hx
  have hx2 : (2:ℝ) ≤ x := by rw [hx]; exact_mod_cast hk2
  have hxA : (16:ℝ)*(A:ℝ)^2 ≤ x := by rw [hx]; exact_mod_cast (show 16*A^2 ≤ k by omega)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 4*(A:ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; nlinarith
  have hlogsq : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hl2 : (1:ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hkey : (A:ℝ) * Real.log x ≤ x * Real.log 2 := by
    have hA0 : (0:ℝ) ≤ A := by positivity
    have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have : (A:ℝ) * Real.log x ≤ (A:ℝ) * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hlogsq hA0
    nlinarith
  set n : ℕ := k ^ (e+1) with hn
  have hn2 : 2 ≤ n := by
    rw [hn]; calc 2 ≤ k := hk2
      _ = k^1 := (pow_one k).symm
      _ ≤ k^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hnx : (n:ℝ) = x^(e+1) := by rw [hn, hx]; push_cast; ring
  have hlogn : Real.log n = (e+1) * Real.log x := by rw [hnx, Real.log_pow]; push_cast; ring
  have hlogn0 : 0 < Real.log n := by rw [hlogn]; positivity
  have hpi := Chebyshev.pi_ge n
  have hlog1 : Real.log ((n:ℝ)+1) ≤ 2 * Real.log n := by
    have hn2' : (2:ℝ) ≤ n := by exact_mod_cast hn2
    rw [show (2:ℝ) * Real.log n = Real.log ((n:ℝ)^2) by rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hxe : (1:ℝ) ≤ x^e := one_le_pow₀ (by linarith)
  have hgoal : (C:ℝ) * x^e ≤ ((n:ℝ) * Real.log 2 - Real.log ((n:ℝ)+1)) / Real.log n := by
    rw [le_div_iff₀ hlogn0]
    have h1 : ((C:ℝ) * x^e + 2) * Real.log n ≤ (n:ℝ) * Real.log 2 := by
      have h2 : (C:ℝ) * x^e + 2 ≤ ((C:ℝ)+2) * x^e := by nlinarith
      have hAc : (A:ℝ) = ((e:ℝ)+1)*((C:ℝ)+2) := by simp [A]
      calc ((C:ℝ) * x^e + 2) * Real.log n ≤ ((C:ℝ)+2) * x^e * Real.log n :=
            mul_le_mul_of_nonneg_right h2 hlogn0.le
        _ = x^e * ((A:ℝ) * Real.log x) := by rw [hlogn, hAc]; ring
        _ ≤ x^e * (x * Real.log 2) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (n:ℝ) * Real.log 2 := by rw [hnx]; ring
    nlinarith
  have := hgoal.trans hpi
  have hcast : ((C * k^e : ℕ) : ℝ) = (C:ℝ) * x^e := by rw [hx]; push_cast; ring
  exact_mod_cast (hcast ▸ this)

theorem solution (e : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 * k ^ e ≤ Nat.primeCounting (k ^ (e + 1)) := by
  obtain ⟨k₀, hk₀⟩ := h49_pi_pow_lower e 2
  exact ⟨k₀, hk₀⟩

