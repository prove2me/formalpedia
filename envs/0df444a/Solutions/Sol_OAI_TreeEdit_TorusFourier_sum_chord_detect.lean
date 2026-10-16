-- Prove2me | solution 1 for OAI.TreeEdit.TorusFourier.sum_chord_detect
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:05:28.495349+00:00
-- url     : https://prove2.me/submissions/cb95c69e-6ac5-456f-89b1-7eecf2fd8c1b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean:L72-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusFourier.sum_chord_detect. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier

-- ---- from OAI.Combinatorics.TreeEdit.CircleFourier ----
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical

lemma character_apply {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) (a : ZMod M) :
    χ a = ZMod.stdAddChar (frequency χ * a) := by
  have hh := AddChar.zmodAddEquiv.apply_symm_apply χ
  change AddChar.zmodAddEquiv (frequency χ) = χ at hh
  calc
    χ a = (AddChar.zmodAddEquiv (frequency χ)) a := congrArg (fun η : AddChar (ZMod M) ℂ => η a) hh.symm
    _ = _ := rfl

lemma centered_cast {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    (centered χ : ZMod M) = frequency χ := ZMod.coe_valMinAbs _

lemma centered_bound {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    |(centered χ : ℝ)| * 2 ≤ M := by
  have hh := (frequency χ).valMinAbs_mem_Ioc
  rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_mul, abs_le]
  constructor
  · exact_mod_cast hh.1.le
  · exact_mod_cast hh.2

lemma chord_lower {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    4 * |(centered χ : ℝ)| / M ≤ ‖1 - χ 1‖ := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hb := centered_bound χ
  rw [character_apply χ 1, mul_one, ← centered_cast χ, ZMod.stdAddChar_coe,
    norm_sub_rev]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (centered χ : ℂ) / (M : ℂ) =
      Complex.I * ((2 * Real.pi * (centered χ : ℝ) / M : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hh := Real.mul_le_sin (x := Real.pi * |(centered χ : ℝ)| / M)
    (by positivity) (by rw [div_le_iff₀ hM]; nlinarith [Real.pi_pos])
  have habs : |Real.sin (2 * Real.pi * (centered χ : ℝ) / M / 2)| =
      Real.sin (Real.pi * |(centered χ : ℝ)| / M) := by
    rw [show 2 * Real.pi * (centered χ : ℝ) / M / 2 = Real.pi * (centered χ : ℝ) / M by ring]
    have hab : |Real.pi * (centered χ : ℝ) / M| = Real.pi * |(centered χ : ℝ)| / M := by
      simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hM]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [hab, div_le_iff₀ hM]; nlinarith [Real.pi_pos]), hab]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), habs]
  have heq : 2 / Real.pi * (Real.pi * |(centered χ : ℝ)| / M) = 2 * |(centered χ : ℝ)| / M := by
    field_simp
  rw [heq] at hh
  calc
    4 * |(centered χ : ℝ)| / M = 2 * (2 * |(centered χ : ℝ)| / M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)

lemma sum_chord_detect {M Q J : ℕ} [NeZero M] (hQ : 0 < Q) (hM : M = J * Q)
    (χ : AddChar (ZMod M) ℂ) (hχ : (Q : ℝ) ≤ |(centered χ : ℝ)|) :
    (J : ℝ) ≤ ∑ a ∈ Finset.range J, (2 - 2 * (χ (a + 1)).re) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hJ : 0 < J := by have := NeZero.pos M; nlinarith
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hleft : 4 ≤ (J : ℝ) * ‖1 - χ 1‖ := by
    have hh := chord_lower χ
    have he : (M : ℝ) = (J : ℝ) * Q := by exact_mod_cast hM
    rw [div_le_iff₀ hMr] at hh
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    nlinarith
  let S : ℂ := ∑ a ∈ Finset.range J, (χ 1) ^ (a + 1)
  have hgeom : S * ((χ 1) - 1) = (χ 1) * ((χ 1) ^ J - 1) := by
    dsimp [S]
    simp only [pow_succ, ← Finset.sum_mul]
    rw [mul_right_comm, geom_sum_mul]
    ring
  have hnorm : ‖S‖ * ‖1 - χ 1‖ ≤ 2 := by
    rw [norm_sub_rev, ← norm_mul, hgeom, norm_mul, χ.norm_apply, one_mul]
    have hh := norm_sub_le ((χ 1) ^ J) (1 : ℂ)
    simpa only [norm_pow, χ.norm_apply, one_pow, norm_one, one_add_one_eq_two] using hh
  have hs : 2 * S.re ≤ J := by
    have hn := norm_nonneg S
    have hc := norm_nonneg (1 - χ 1)
    have hr := Complex.re_le_norm S
    nlinarith [mul_le_mul_of_nonneg_left hleft hn, mul_le_mul_of_nonneg_right hr hc]
  have he (a : ℕ) : χ ((a + 1 : ℕ) : ZMod M) = (χ 1) ^ (a + 1) := by
    rw [show ((a + 1 : ℕ) : ZMod M) = (a + 1) • (1 : ZMod M) by simp [nsmul_eq_mul], AddChar.map_nsmul_eq_pow]
  have hre : ∑ a ∈ Finset.range J, (χ (a + 1)).re = S.re := by
    simp only [Nat.cast_add, Nat.cast_one] at he
    simp_rw [he]
    simp only [S, Complex.re_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, hre]
  linarith

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical
open TorusTree

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

end TreeEdit.TorusFourier

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusFourier.sum_chord_detect := @_root_.OAI.TreeEdit.TorusFourier.sum_chord_detect
