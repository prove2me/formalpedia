-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_pow_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:30:12.304345+00:00
-- url     : https://prove2.me/submissions/ace70d46-23cb-446a-9dc2-6fc2be14140f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L35-L80
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_pow_lower. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_prime_counting_lower

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- At polynomial arguments, the prime count eventually dominates twice the
preceding power. This is a convenient intermediate form for interval counts. -/
theorem prime_counting_pow_lower (e : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 * k ^ e ≤ Nat.primeCounting (k ^ (e + 1)) := by
  obtain ⟨c, hc, x₀, hmain⟩ := prime_counting_lower
  have hden : 0 < 2 * ((e + 1 : ℕ) : ℝ) := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound (div_pos hc hden)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max 2 (max x₀ a))
  refine ⟨k₀, ?_⟩
  intro k hk
  have hkcast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hklarge : max 2 (max x₀ a) ≤ (k : ℝ) := le_trans hk₀.le hkcast
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_max_left _ _) hklarge
  have hkx : x₀ ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hklarge
  have hka : a ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hklarge
  have hkzero : (0 : ℝ) ≤ k := by positivity
  have hbound := ha (k : ℝ) hka
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hkzero] at hbound
  have hlogbound : Real.log (k : ℝ) ≤
      c / (2 * ((e + 1 : ℕ) : ℝ)) * k := (le_abs_self _).trans hbound
  have hscaled : Real.log (k : ℝ) * (2 * ((e + 1 : ℕ) : ℝ)) ≤ c * k := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using hlogbound
  have hkpow : (k : ℝ) ≤ (k : ℝ) ^ (e + 1) :=
    le_self_pow₀ (by linarith) (by omega)
  have hcount := hmain ((k : ℝ) ^ (e + 1)) (hkx.trans hkpow)
  have hlogpos : 0 < Real.log ((k : ℝ) ^ (e + 1)) :=
    Real.log_pos (one_lt_pow₀ (by linarith) (by omega))
  have hcompare : 2 * (k : ℝ) ^ e ≤ c * (k : ℝ) ^ (e + 1) /
      Real.log ((k : ℝ) ^ (e + 1)) := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      2 * (k : ℝ) ^ e * Real.log ((k : ℝ) ^ (e + 1)) =
          (k : ℝ) ^ e * (Real.log (k : ℝ) * (2 * ((e + 1 : ℕ) : ℝ))) := by
        rw [Real.log_pow]
        ring
      _ ≤ (k : ℝ) ^ e * (c * k) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = c * (k : ℝ) ^ (e + 1) := by rw [pow_succ]; ring
  have hreal := hcompare.trans hcount
  norm_cast at hreal
  simpa only [Nat.floor_natCast] using hreal

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_pow_lower := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_pow_lower
