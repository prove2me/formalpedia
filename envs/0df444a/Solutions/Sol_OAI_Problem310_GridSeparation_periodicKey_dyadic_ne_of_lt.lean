-- Prove2me | solution 1 for OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:30:51.025979+00:00
-- url     : https://prove2.me/submissions/30daf0f8-5aeb-4fe8-b1ac-f5ca22a945d9

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean:L108-L139
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_ne_of_separated

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

lemma periodicKey_ne_of_small_shift {q x d : ℝ} (hq : 4 ≤ q)
    (hlo : 1 ≤ q * d) (hhi : d ≤ 1 / 4) :
    periodicKey q x ≠ periodicKey q (x + d) := by
  apply periodicKey_ne_of_separated (by linarith)
  · simpa using hlo
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ q by linarith)
    have : q * d ≤ q - 1 := by nlinarith
    simpa using this

lemma mesh_mul_dyadic (b : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 : ℝ)⁻¹ ^ b = 4 := by
  rw [pow_add, inv_pow]
  have hb : (2 : ℝ) ^ b ≠ 0 := by positivity
  field_simp
  ring

lemma mesh_ge_four (b : ℕ) : 4 ≤ (2 : ℝ) ^ (b + 2) := by
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith

lemma dyadic_shift_le_quarter {n : ℕ} {t : ℝ} (hn : 3 ≤ n)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) : t * (2 : ℝ)⁻¹ ^ n ≤ 1 / 4 := by
  have hp : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  norm_num at hp
  have hnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

lemma dyadic_gap_ge_smaller {n m : ℕ} (hnm : n < m) :
    (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m := by
  have hp : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [pow_succ] at hp
  norm_num at hp
  linarith

/-- Different indices in one window use different periodic keys, uniformly in
all normalized scales. No exclusion of grid-boundary centers is needed. -/
lemma periodicKey_dyadic_ne_of_lt {b n m : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnm : n < m) (hmhi : m ≤ b)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ m) := by
  have hgap := dyadic_gap_ge_smaller hnm
  have hmon : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmhi
  have hmpos : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hqpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hdiff : (2 : ℝ)⁻¹ ^ b ≤
      t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m := by
    have hprod := mul_nonneg (sub_nonneg.mpr htlo)
      (show 0 ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m by linarith)
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left hdiff hqpos.le
  rw [mesh_mul_dyadic] at hlow
  have hsmall : t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m ≤ 1 / 4 := by
    have := dyadic_shift_le_quarter hnlo htlo hthi
    have hprod : 0 ≤ t * (2 : ℝ)⁻¹ ^ m := mul_nonneg (by linarith) hmpos.le
    linarith
  have hne := periodicKey_ne_of_small_shift
    (x := x + t * (2 : ℝ)⁻¹ ^ m) (mesh_ge_four b)
    (show 1 ≤ (2 : ℝ) ^ (b + 2) *
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) by linarith) hsmall
  have heq : x + t * (2 : ℝ)⁻¹ ^ m +
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) =
      x + t * (2 : ℝ)⁻¹ ^ n := by ring
  rw [heq] at hne
  exact hne.symm

end Problem310.GridSeparation

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.GridSeparation


theorem solution : type_of% @_root_.OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt := @_root_.OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt
