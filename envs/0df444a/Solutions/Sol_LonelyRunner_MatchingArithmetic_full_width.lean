-- Prove2me | solution 1 for LonelyRunner.MatchingArithmetic.full_width
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:44.113982+00:00
-- url     : https://prove2.me/submissions/a42fa66c-b07b-4b28-a4a1-1e6de867048e

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















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
open LonelyRunner.MatchingArithmetic

set_option maxHeartbeats 1000000 in
/-- The common-divisor constraints make the safe interval too long to be
covered by one slow band and two fast bands. -/
theorem solution {n r s g w F : ℝ}
    (hg : 2 ≤ g) (hrg : 2*g ≤ r) (hgs : r+g ≤ s) (hsn : s+1 ≤ n)
    (hw : 0 < w) (hmul : r*s ≤ g*w)
    (hF : (n ≤ 2*r-1 ∧ F=r-1) ∨ (n=2*r ∧ F=2*r-1)) :
    (2*(1/n)/w)*(1+4/(n-2)) <
      (n-r)/(n*r*(r+1)) + (n-r)/(n*r*F) := by
  have hg0 : 0 < g := by linarith
  have hr : 0 < r := by linarith
  have hn : 0 < n := by linarith
  have hnm : 0 < n-2 := by linarith
  have ha : 0 < n-r := by linarith
  have hrp : 0 < r+1 := by linarith
  have hrm : 0 < r-1 := by linarith
  have hgr : 0 < g*r := mul_pos hg0 hr
  have hscale : 0 < 2*(1/n)/w := by positivity
  have hF0 : 0 < F := by rcases hF with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> linarith
  have heq : (n-r)/(n*r*(r+1)) + (n-r)/(n*r*F) =
      (2*(1/n)/w) * ((n-r)*w/(2*r)*(1/(r+1)+1/F)) := by
    field_simp
  rw [heq]
  apply mul_lt_mul_of_pos_left _ hscale
  rcases hF with ⟨hboundary,rfl⟩ | ⟨hboundary,rfl⟩
  · have hbase : g*r+5*g ≤ (n-r)*s := by
      nlinarith [mul_nonneg (show 0 ≤ n-r-(g+1) by linarith) (show 0 ≤ s by linarith),
        mul_nonneg (show 0 ≤ g+1 by linarith) (show 0 ≤ s-(r+g) by linarith),
        mul_nonneg hg0.le (show 0 ≤ g-2 by linarith)]
    have hratio : 1+5/r ≤ (n-r)*s/(g*r) := by
      apply (le_div_iff₀ hgr).mpr
      field_simp
      nlinarith only [hbase]
    have hstrict : 1+4/(n-2) < 1+5/r := by
      have h : 4/(n-2) < 5/r := (div_lt_div_iff₀ hnm hr).mpr (by linarith)
      linarith
    have hprod : (n-r)*s/(g*r) ≤ (n-r)*w/(r*r) := by
      apply (div_le_div_iff₀ hgr (mul_pos hr hr)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hmul (mul_nonneg ha.le hr.le)]
    have hden : 0 < r*r-1 := by nlinarith
    have hlast : (n-r)*w/(r*r) ≤ (n-r)*w/(r*r-1) :=
      div_le_div_of_nonneg_left (mul_nonneg ha.le hw.le) hden (by linarith)
    have heq' : (n-r)*w/(2*r)*(1/(r+1)+1/(r-1)) = (n-r)*w/(r*r-1) := by
      field_simp (disch := nlinarith)
      ring
    rw [heq']
    exact lt_of_lt_of_le (lt_of_lt_of_le hstrict hratio) (le_trans hprod hlast)
  · have hf : 0 < 2*r-1 := by linarith
    have hharm : 4/(3*r) ≤ 1/(r+1)+1/(2*r-1) := by
      have heqH : 1/(r+1)+1/(2*r-1) = 3*r/((r+1)*(2*r-1)) := by
        field_simp (disch := nlinarith)
        ring
      rw [heqH]
      apply (div_le_div_iff₀ (by positivity : 0 < 3*r) (mul_pos hrp hf)).mpr
      nlinarith only [sq_nonneg (r-2)]
    have hwg : 3*r ≤ w := by
      have h : g*(3*r) ≤ g*w := by
        nlinarith only [hmul, mul_le_mul_of_nonneg_left hgs hr.le,
          mul_le_mul_of_nonneg_left hrg hr.le]
      exact (mul_le_mul_iff_right₀ hg0).mp h
    have htwo : 2 ≤ (n-r)*w/(2*r)*(1/(r+1)+1/(2*r-1)) := by
      have hpre := mul_le_mul_of_nonneg_left hharm (show 0 ≤ (n-r)*w/(2*r) by positivity)
      have heq' : (n-r)*w/(2*r)*(4/(3*r)) = 2*w/(3*r) := by rw [hboundary]; field_simp; ring
      rw [heq'] at hpre
      have htwo' : 2 ≤ 2*w/(3*r) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      exact le_trans htwo' hpre
    have hlt : 1+4/(n-2) < 2 := by
      have : 4/(n-2) < 1 := (div_lt_one hnm).mpr (by linarith)
      linarith
    exact lt_of_lt_of_le hlt htwo
