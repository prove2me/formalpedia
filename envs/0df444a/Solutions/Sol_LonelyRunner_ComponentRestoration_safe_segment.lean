-- Prove2me | solution 1 for LonelyRunner.ComponentRestoration.safe_segment
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:27.017988+00:00
-- url     : https://prove2.me/submissions/12293968-265a-4041-a960-672b0087a4bb

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner









theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m





















/-- The usual "interval" description: for `δ ≤ 1/2`, `δ ≤ ‖x‖` iff `x mod 1 ∈ [δ, 1 - δ]`. -/
theorem le_ndist_iff_fract {δ x : ℝ} : δ ≤ ndist x ↔ δ ≤ Int.fract x ∧ δ ≤ 1 - Int.fract x := by
  rw [ndist_eq_min_fract, le_min_iff]



/-- Conversely, `δ ≤ ‖x‖` puts `x` in `[⌊x⌋ + δ, ⌊x⌋ + 1 - δ]`. -/
theorem floor_bounds_of_le_ndist {x δ : ℝ} (h : δ ≤ ndist x) :
    (⌊x⌋ : ℝ) + δ ≤ x ∧ x ≤ ⌊x⌋ + 1 - δ := by
  rw [le_ndist_iff_fract] at h
  have := Int.self_sub_floor x
  rw [Int.fract] at h
  constructor <;> linarith [h.1, h.2]









end LonelyRunner

namespace LonelyRunner.BadCover





theorem strict_of_between {x δ : ℝ} {m : ℤ}
    (hl : (m : ℝ) + δ < x) (hu : x < m + 1 - δ) : δ < ndist x := by
  change δ < |x - (round x : ℤ)|
  rcases le_or_gt (round x) m with h | h
  · have hR : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have hR : (m : ℝ) + 1 ≤ (round x : ℤ) := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey



















end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover





























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion























end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

























end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth















end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth











end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

















end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.ComponentRestoration
open SeparatedMulti InteractionComponents

/-- A retained speed stays strictly safe between a nearby primitive center
and any strictly safe point in the deleted speed's bad band. -/
theorem solution {n r v : ℕ} {a : ℤ} {t u : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrn : r < n) (hvn : v < n)
    (hcenter : 1/(r:ℝ) ≤ ndist ((v:ℝ)*((a:ℝ)/r)))
    (hbad : |(r:ℝ)*t-a| ≤ 1/(n:ℝ))
    (hsafe : 1/(n:ℝ) < ndist ((v:ℝ)*t))
    (hu : u ∈ Set.Icc (min t ((a:ℝ)/r)) (max t ((a:ℝ)/r))) :
    1/(n:ℝ) < ndist ((v:ℝ)*u) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hvR : (0:ℝ) ≤ v := Nat.cast_nonneg v
  have hδ : 1/(n:ℝ) < 1/(r:ℝ) := by
    apply one_div_lt_one_div_of_lt hrR
    exact_mod_cast hrn
  let x : ℝ := (a:ℝ)/r
  let j : ℤ := ⌊(v:ℝ)*x⌋
  have hc := floor_bounds_of_le_ndist hcenter
  change (j:ℝ)+1/(r:ℝ) ≤ (v:ℝ)*x ∧ (v:ℝ)*x ≤ j+1-1/(r:ℝ) at hc
  have hid : (r:ℝ)*|(v:ℝ)*t-(v:ℝ)*x| = (v:ℝ)*|(r:ℝ)*t-a| := by
    calc
      _ = |(r:ℝ)*((v:ℝ)*t-(v:ℝ)*x)| := by rw [abs_mul,abs_of_pos hrR]
      _ = |(v:ℝ)*((r:ℝ)*t-a)| := by congr 1; dsimp [x]; field_simp
      _ = _ := by rw [abs_mul,abs_of_nonneg hvR]
  have hnear : |(v:ℝ)*t-(v:ℝ)*x| < 1/(r:ℝ) := by
    apply (lt_div_iff₀ hrR).mpr
    have hmul := mul_le_mul_of_nonneg_left hbad hvR
    have hlt : (v:ℝ)*(1/(n:ℝ)) < 1 := by
      rw [mul_one_div,div_lt_one hnR]
      exact_mod_cast hvn
    nlinarith only [hid,hmul,hlt]
  have hband : (j:ℝ) < (v:ℝ)*t ∧ (v:ℝ)*t < j+1 := by
    obtain ⟨hlo,hhi⟩ := abs_lt.mp hnear
    constructor <;> linarith [hc.1,hc.2]
  have htlo : (j:ℝ)+1/(n:ℝ) < (v:ℝ)*t := by
    have hh := hsafe.trans_le (ndist_le_abs_sub ((v:ℝ)*t) j)
    rw [abs_of_pos (by linarith : 0 < (v:ℝ)*t-j)] at hh
    linarith
  have hthi : (v:ℝ)*t < (j:ℝ)+1-1/(n:ℝ) := by
    have hh := hsafe.trans_le (ndist_le_abs_sub ((v:ℝ)*t) (j+1))
    push_cast at hh
    rw [abs_of_neg (by linarith : (v:ℝ)*t-((j:ℝ)+1) < 0)] at hh
    linarith
  apply BadCover.strict_of_between (m := j)
  all_goals
    change min t x ≤ u ∧ u ≤ max t x at hu
    rcases le_total t x with htx | hxt
    · rw [min_eq_left htx,max_eq_right htx] at hu
      have hl := mul_le_mul_of_nonneg_left hu.1 hvR
      have hh := mul_le_mul_of_nonneg_left hu.2 hvR
      linarith [hc.1,hc.2]
    · rw [min_eq_right hxt,max_eq_left hxt] at hu
      have hl := mul_le_mul_of_nonneg_left hu.1 hvR
      have hh := mul_le_mul_of_nonneg_left hu.2 hvR
      linarith [hc.1,hc.2]
