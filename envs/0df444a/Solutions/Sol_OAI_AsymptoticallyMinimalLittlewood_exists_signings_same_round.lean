-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:40:10.872453+00:00
-- url     : https://prove2.me/submissions/8d6fc512-8d8a-48ad-96d6-e764ac627183

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L426-L511
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_card_good_cost
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_entropy_log_parameters
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_same_code_far
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exp_small_lt_half_cube
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_signing_round_sum_le

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Entropy supplies two widely separated signings with identical rounded row sums. -/
theorem exists_signings_same_round {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 32 ≤ Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    let d := 64 * Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    ∃ x y : α → Bool, (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) ∧
      ∀ i, round ((∑ k, B i k * boolSign (x k)) / d) =
        round ((∑ k, B i k * boolSign (y k)) / d) := by
  classical
  let s : ℝ := Fintype.card α
  let R : ℝ := Fintype.card β
  let L := Real.log (16 * R / s)
  let d := 64 * Real.sqrt (s * L)
  let t := d / (4 * s)
  let M := s / (256 * L)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast (by omega : 0 < Fintype.card α)
  have hsR' : s ≤ R := by dsimp [s, R]; exact_mod_cast hsR
  obtain ⟨hL, hdecay, hmean, hpart⟩ := entropy_log_parameters hs0 hsR'
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hd2 : d ^ 2 = 4096 * s * L := by
    dsimp [d]
    nlinarith [Real.sq_sqrt (show 0 ≤ s * L by positivity)]
  have htd_eq : t * d = 1024 * L := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (show 4 * s ≠ 0 by positivity)).mpr
    nlinarith [hd2]
  have htd : 4 ≤ t * d := by rw [htd_eq]; linarith
  have hexponent : t ^ 2 * s / 2 - t * d / 4 = -128 * L := by
    rw [htd_eq]
    have ht2 : t ^ 2 * s = 256 * L := by
      calc
        _ = d ^ 2 / (16 * s) := by dsimp [t]; field_simp; ring
        _ = 256 * L := by rw [hd2]; field_simp; ring
    rw [ht2]
    ring
  let code : (α → Bool) → β → ℤ := fun x i ↦
    round ((∑ k, B i k * boolSign (x k)) / d)
  let cost : (α → Bool) → ℝ := fun x ↦ ∑ i, |(code x i : ℝ)|
  have hcost0 : ∀ x, 0 ≤ cost x := fun x ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hcostsum : (∑ x, cost x) ≤ (2 : ℝ) ^ Fintype.card α * M / 2 := by
    have hrow (i : β) : (∑ x : α → Bool, |(code x i : ℝ)|) ≤
        (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) := by
      have h := signing_round_sum_le (B i) (hB i) hd ht htd
      change _ ≤ (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (t ^ 2 * s / 2 - t * d / 4)) at h
      rwa [hexponent] at h
    calc
      _ = ∑ i, ∑ x : α → Bool, |(code x i : ℝ)| := Finset.sum_comm
      _ ≤ ∑ _i : β, (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = (2 : ℝ) ^ Fintype.card α * (2 * R * Real.exp (-128 * L)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [R]
        ring
      _ ≤ (2 : ℝ) ^ Fintype.card α * (s / (512 * L)) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by dsimp [M]; ring
  let G := Finset.univ.filter fun x ↦ cost x ≤ M
  have hM : 0 < M := by dsimp [M]; positivity
  have hG : (2 : ℝ) ^ Fintype.card α / 2 ≤ (G.card : ℝ) := by
    have hc : (Fintype.card (α → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card α := by simp
    have hh := card_good_cost cost hcost0 hM
    rw [hc] at hh
    exact hh hcostsum
  have haM : (4 * L) * M = s / 64 := by
    dsimp [M]
    field_simp
    ring
  have hlarge : Real.exp ((4 * L) * M + 4 * Fintype.card β * Real.exp (-(4 * L)) +
      3 * Fintype.card α / 8) < (G.card : ℝ) := by
    apply lt_of_lt_of_le _ hG
    apply lt_of_le_of_lt _ (exp_small_lt_half_cube hs)
    apply Real.exp_le_exp.mpr
    rw [haM]
    change s / 64 + 4 * R * Real.exp (-(4 * L)) + 3 * s / 8 ≤ 13 * s / 32
    have hp : 4 * R * Real.exp (-(4 * L)) ≤ s / 64 := by simpa only [neg_mul] using hpart
    linarith
  obtain ⟨x, hx, y, hy, hxy, hfar⟩ := exists_same_code_far G code
    (show 0 ≤ 4 * L by positivity) (by simpa only [neg_mul] using hdecay)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) hlarge
  exact ⟨x, y, hfar, fun i ↦ congrFun hxy i⟩

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round.{u,v}
