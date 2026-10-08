-- Prove2me | solution 1 for LonelyRunner.SmallComponentRigidity.strict_or_gw_tight
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T19:06:33.689784+00:00
-- url     : https://prove2.me/submissions/ba2572b8-d110-4828-88af-dadbf0840897

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_SmallComponentRigidity_matching_windows

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m



















/-- `δ ≤ ‖x‖` iff `x` is at distance at least `δ` from every integer. -/
theorem le_ndist_iff {δ x : ℝ} : δ ≤ ndist x ↔ ∀ m : ℤ, δ ≤ |x - m| :=
  ⟨fun h m => h.trans (ndist_le_abs_sub x m), fun h => h (round x)⟩















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







/-- A valid GW window ends no later than r-1. At n=2r even the window
with multiplier two contains the unit r+1, so equality is impossible. -/
theorem gw_window_bound {n r m : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m)
    (hgw : GW n r m) : m*(n-r) ≤ r-1 := by
  have hr : 2 ≤ r := by omega
  have hfirst : m*(n-r) ≤ r+1 := by
    by_contra! hh
    exact hgw (r+1) (by omega) hh (by simp)
  have hstrict : n < 2*r := by
    by_contra! hh
    have heq : n-r=r := by omega
    rw [heq] at hfirst
    nlinarith
  have hcop : Nat.Coprime r (r-1) :=
    (Nat.coprime_self_sub_right (show 1 ≤ r by omega)).mpr (by simp)
  by_contra! hh
  exact hgw (r-1) (by omega) hh hcop





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



/-- A primitive r-grid center has distance at least 1/r for nonmultiples. -/
theorem primitive_center_bound {r v b : ℕ} {a c : ℤ}
    (hr : 0 < r) (hu : a*(b:ℤ)-c*(r:ℤ)=1) (hnot : ¬ r ∣ v) :
    1/(r:ℝ) ≤ ndist ((v:ℝ)*((a:ℝ)/r)) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [le_ndist_iff]
  intro j
  have hne : (v:ℤ)*a-(r:ℤ)*j ≠ 0 := by
    intro heq
    apply hnot
    have hd : (r:ℤ) ∣ (v:ℤ) := by
      refine ⟨(b:ℤ)*j-c*v,?_⟩
      nlinarith [congrArg (fun x : ℤ => x*v) hu]
    exact_mod_cast hd
  have hunit : (1:ℝ) ≤ |(v:ℝ)*a-(r:ℝ)*j| := by
    exact_mod_cast (show (1:ℤ) ≤ |(v:ℤ)*a-(r:ℤ)*j| by
      have := abs_pos.mpr hne
      omega)
  have hid : |(v:ℝ)*a-(r:ℝ)*j| = r*|(v:ℝ)*((a:ℝ)/r)-j| := by
    calc
      _ = |(r:ℝ)*((v:ℝ)*((a:ℝ)/r)-j)| := by congr 1; field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hrR]
  apply (div_le_iff₀ hrR).mpr
  rw [hid] at hunit
  simpa only [mul_comm] using hunit





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





















/-- A valid GW acceleration cannot land on a multiple of n. -/
theorem not_dvd_acceleration {n r m : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hgw : GW n r m) : ¬ n ∣ m*r := by
  intro hd
  have hwin := MixedReplacements.gw_window_bound hn hlarge hrn hm hgw
  have hpos : 0 < m*(n-r) := Nat.mul_pos (by omega) (by omega)
  have hd' : n ∣ m*(n-r) := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_sub (dvd_mul_left n m) hd
  have hle := Nat.le_of_dvd hpos hd'
  omega



/-- A GW matching supplies the explicit weak time t=1/n. -/
theorem grid_time_of_matching {n : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hmatch : ∃ f : ℕ → ℕ, Set.BijOn f (R : Set ℕ) (W : Set ℕ) ∧
      ∀ r ∈ R, ∃ m : ℕ, 2 ≤ m ∧ f r=m*r ∧ GW n r m) :
    WeakAt n R W (1/(n:ℝ)) := by
  obtain ⟨f,hbij,hf⟩ := hmatch
  intro v hv
  have hnot : ¬ n ∣ v := by
    rcases hv with ⟨hv,hvn,_⟩ | hvW
    · intro hd
      have := Nat.le_of_dvd hv hd
      omega
    · obtain ⟨r,hrR,hfr⟩ := hbij.2.2 hvW
      obtain ⟨m,hm,heq,hgw⟩ := hf r hrR
      rw [← hfr,heq]
      exact not_dvd_acceleration hn (hR r hrR).1 (hR r hrR).2 hm hgw
  simpa only [Int.cast_one] using ComponentRestoration.primitive_center_bound
    (r := n) (a := 1) (b := 1) (c := 0) (by omega) (by norm_num) hnot











end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.SmallComponentRigidity
open SeparatedMulti SeparatedReplacements InteractionComponents

/-- The complete rigidity alternative in one statement: strict improvement,
or a GW matching together with an attained, globally sharp threshold. -/
theorem solution {n : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hW : ∀ p ∈ W, n ≤ p) (hparts : PairComponents n W)
    (hcard : R.card=W.card) :
    HasStrictTime n R W ∨
      (¬ HasStrictTime n R W ∧ WeakAt n R W (1/(n:ℝ)) ∧
        ∃ f : ℕ → ℕ, Set.BijOn f (R : Set ℕ) (W : Set ℕ) ∧
          ∀ r ∈ R, ∃ m : ℕ, 2 ≤ m ∧ f r=m*r ∧ GW n r m) := by
  by_cases hh : HasStrictTime n R W
  · exact Or.inl hh
  · have hmatch := matching_windows hn hR hW hparts hcard hh
    exact Or.inr ⟨hh,grid_time_of_matching hn hR hmatch,hmatch⟩
