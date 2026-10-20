-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:22:41.284481+00:00
-- url     : https://prove2.me/submissions/32fe51cc-e3af-4306-b339-8765ff4b9f58

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteParameters.lean:L195-L218
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_exists_finiteLength_bracket
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_finite_cap_sqrt_bound

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteParameters ----
namespace OAI

namespace TreeEdit.BinaryLower.Parameters

lemma le_finiteLength {k : ℕ} (hk : 0 < k) : k ≤ finiteLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow (by omega : 0 < 3 * k))

lemma finite_lower_log_bound {c₀ : ℝ} (hc₀ : 0 < c₀) {k : ℕ}
    (hk : 20 ≤ k) (hkc : -4 * Real.log c₀ ≤ (k : ℝ)) :
    (1 / 4 : ℝ) * k * Real.log k ≤
      Real.log (c₀ * ((k : ℝ) / 4) ^ k) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlog1 : 1 ≤ Real.log (k : ℝ) := by
    apply (Real.le_log_iff_exp_le hkpos).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hlog4 : 2 * Real.log 4 ≤ Real.log (k : ℝ) := by
    calc
      2 * Real.log 4 = Real.log ((4 : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_mul hc₀.ne' (by positivity), Real.log_pow,
    Real.log_div hkpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  have hmul1 := mul_le_mul_of_nonneg_left hlog1 (le_of_lt hkpos)
  have hmul4 := mul_le_mul_of_nonneg_left hlog4 (le_of_lt hkpos)
  nlinarith

/-- Numerical transfer from a finite-family distortion to an intervening cap. -/
lemma finite_cap_exponential_bound {c₀ : ℝ} (hc₀ : 0 < c₀) {k d : ℕ}
    (hk : 20 ≤ k) (hkc : -4 * Real.log c₀ ≤ (k : ℝ))
    (hd : 2 ≤ d) (hcap : d ≤ finiteLength (k + 1)) :
    Real.exp ((1 / 160 : ℝ) *
      Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
        c₀ * ((k : ℝ) / 4) ^ k := by
  have hsqrt := finite_cap_sqrt_bound hk hd hcap
  have hlower := finite_lower_log_bound hc₀ hk hkc
  have hexponent : (1 / 160 : ℝ) *
      Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
        Real.log (c₀ * ((k : ℝ) / 4) ^ k) := by nlinarith only [hsqrt, hlower]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ Real.exp (Real.log (c₀ * ((k : ℝ) / 4) ^ k)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := Real.exp_log (by positivity)

/-- The complete numerical all-large-cap selection used after constructing the
finite-tree witness family.  The requested lower threshold `K` is arbitrary. -/
lemma exists_finite_cap_parameters {c₀ : ℝ} (hc₀ : 0 < c₀) (K : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ k : ℕ,
      K ≤ k ∧ 20 ≤ k ∧ finiteLength k ≤ d ∧
        Real.exp ((1 / 160 : ℝ) *
          Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
            c₀ * ((k : ℝ) / 4) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-4 * Real.log c₀)
  let k₀ : ℕ := max 20 (max K n)
  have hk20 : 20 ≤ k₀ := le_max_left _ _
  have hkK : K ≤ k₀ := (le_max_left K n).trans (le_max_right 20 (max K n))
  have hkn : n ≤ k₀ := (le_max_right K n).trans (le_max_right 20 (max K n))
  refine ⟨finiteLength k₀, ?_⟩
  intro d hd
  obtain ⟨k, hk₀, hkd, hdk⟩ := exists_finiteLength_bracket (by omega : 0 < k₀) hd
  have hk : 20 ≤ k := hk20.trans hk₀
  have hkc : -4 * Real.log c₀ ≤ (k : ℝ) :=
    hn.trans (Nat.cast_le.mpr (hkn.trans hk₀))
  have hd2 : 2 ≤ d := by
    have := le_finiteLength (by omega : 0 < k)
    omega
  exact ⟨k, hkK.trans hk₀, hk, hkd,
    finite_cap_exponential_bound hc₀ hk hkc hd2 hdk.le⟩

end TreeEdit.BinaryLower.Parameters

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters := @_root_.OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters
