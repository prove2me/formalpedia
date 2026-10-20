-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:19:42.273526+00:00
-- url     : https://prove2.me/submissions/d4612724-5eb3-48c3-8a00-016622495409

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


theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  refine ⟨Real.log 2 / 2, by positivity, 400, fun x hx => ?_⟩
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := Chebyshev.psi_le_primeCounting_mul_log' x
  have h2 := Chebyshev.psi_ge' (x := x) (by linarith)
  have hy : (0:ℝ) < x + 2 := by linarith
  have hr := Real.sq_sqrt hy.le
  have hr0 := Real.sqrt_nonneg (x + 2)
  have hsq : Real.sqrt (x+2) ≤ (x+2)/20 := by nlinarith
  have hlog : Real.log (x+2) ≤ 2 * Real.sqrt (x+2) := by
    have e : Real.log (Real.sqrt (x+2)) = Real.log (x+2) / 2 := Real.log_sqrt hy.le
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
    linarith
  have hl2 := Real.log_two_gt_d9
  have hm : 0.69 * (x/2 - 1) ≤ Real.log 2 * (x/2 - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hcx : Real.log 2 / 2 * x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x := by nlinarith
  rw [div_le_iff₀ hlogx]
  exact hcx

