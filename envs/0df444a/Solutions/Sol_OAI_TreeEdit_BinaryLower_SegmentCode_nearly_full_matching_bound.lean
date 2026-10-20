-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.SegmentCode.nearly_full_matching_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:18:49.875657+00:00
-- url     : https://prove2.me/submissions/5f175baf-e189-40df-8c23-9487a7aa9aba

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open Finset
theorem h49_choose_mul_pow_le (n k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    (n.choose k : ℝ) * x^k ≤ (x+1)^n := by
  rw [add_pow]
  have ht : k ∈ Finset.range (n+1) := Finset.mem_range.2 (by omega)
  calc (n.choose k : ℝ) * x^k = x^k * 1^(n-k) * (n.choose k) := by ring
    _ ≤ ∑ m ∈ Finset.range (n+1), x^m * 1^(n-m) * (n.choose m) :=
      Finset.single_le_sum (f := fun m => x^m * 1^(n-m) * (n.choose m : ℝ))
        (fun m _ => by positivity) ht

theorem solution (a s : ℕ) (hs : s ≤ a)
    (hlarge : 99*a ≤ 100*s) :
    (a.choose s : ℝ)^2 * (1/2 : ℝ)^s ≤ (9/10 : ℝ)^a := by
  obtain ⟨t, rfl⟩ : ∃ t, a = s + t := ⟨a - s, by omega⟩
  have ht : 99 * t ≤ s := by omega
  rw [Nat.choose_symm_add]
  have hC := h49_choose_mul_pow_le (s+t) t (by omega) (1/100) (by norm_num)
  have hC' : ((s+t).choose t : ℝ) ≤ (101/100)^(s+t) * 100^t := by
    have h100 : (1/100:ℝ)^t * 100^t = 1 := by rw [← mul_pow]; norm_num
    calc ((s+t).choose t : ℝ) = ((s+t).choose t : ℝ) * (1/100)^t * 100^t := by
          rw [mul_assoc, h100, mul_one]
      _ ≤ (1/100 + 1)^(s+t) * 100^t := by gcongr
      _ = (101/100)^(s+t) * 100^t := by norm_num
  have hA : ((101/100:ℝ)^2 * (5/9))^s ≤ ((101/100:ℝ)^2 * (5/9))^(99*t) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  have hAB : ((101/100:ℝ)^2 * (5/9))^99 * ((101/100)^2 * (100000/9)) ≤ 1 := by norm_num
  have hkey : ((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t ≤ 1 := by
    calc ((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t
        ≤ ((101/100:ℝ)^2 * (5/9))^(99*t) * ((101/100)^2 * (100000/9))^t := by gcongr
      _ = (((101/100:ℝ)^2 * (5/9))^99 * ((101/100)^2 * (100000/9)))^t := by
          rw [pow_mul, ← mul_pow]
      _ ≤ 1 := pow_le_one₀ (by positivity) hAB
  have g1 : ∀ (p q r : ℝ), (p^(s+t) * q^t)^2 * r^s = (p^2*r)^s * (p^2*q^2)^t := by intros; ring
  have g2 : ∀ (c A B : ℝ), (c*A)^s * (c*B)^t = c^(s+t) * (A^s * B^t) := by intros; ring
  have hexp : ((101/100:ℝ)^(s+t) * 100^t)^2 * (1/2)^s
      = (9/10:ℝ)^(s+t) * (((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t) := by
    rw [g1, ← g2]; norm_num
  calc ((s+t).choose t : ℝ)^2 * (1/2)^s ≤ ((101/100:ℝ)^(s+t) * 100^t)^2 * (1/2)^s := by gcongr
    _ = _ := hexp
    _ ≤ (9/10:ℝ)^(s+t) * 1 := by gcongr
    _ = _ := mul_one _

