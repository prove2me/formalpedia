-- Prove2me | solution 1 for LonelyRunner.BadCover.fast_center_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:30.928983+00:00
-- url     : https://prove2.me/submissions/14ac1bbc-317b-44c9-986d-de1d5f9113d4

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner









theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m

@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]











/-- On `[0, 1/2]` the distance to the nearest integer is the identity. -/
theorem ndist_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ndist x = x := by
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨h0, by linarith⟩
  rw [ndist_eq_min_fract, hfr]
  exact min_eq_left (by linarith)

@[simp] theorem ndist_half : ndist (1 / 2) = 1 / 2 := ndist_of_mem (by norm_num) le_rfl

















end LonelyRunner

namespace LonelyRunner.BadCover



theorem band_center_unique {x δ : ℝ} {c d : ℤ} (hδ : 2 * δ < 1)
    (hc : |x - c| ≤ δ) (hd : |x - d| ≤ δ) : c = d := by
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  have hh : |(c : ℝ) - d| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hhZ : |c - d| < 1 := by exact_mod_cast hh
  have := abs_lt.mp hhZ
  omega

theorem strict_of_between {x δ : ℝ} {m : ℤ}
    (hl : (m : ℝ) + δ < x) (hu : x < m + 1 - δ) : δ < ndist x := by
  change δ < |x - (round x : ℤ)|
  rcases le_or_gt (round x) m with h | h
  · have hR : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have hR : (m : ℝ) + 1 ≤ (round x : ℤ) := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- A whole interval of bad times for one positive speed stays in one band. -/
theorem single_band {A B w δ : ℝ} (hw : 0 < w) (hδ : δ < 1 / 2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (w * t) ≤ δ) :
    ∃ k : ℤ, ∀ t ∈ Set.Icc A B, |w * t - k| ≤ δ := by
  let k : ℤ := round (w * A)
  have hA : |w * A - k| ≤ δ := hcover A ⟨le_rfl, hAB⟩
  have hAl := (abs_le.mp hA).1
  have hAu := (abs_le.mp hA).2
  have hB : w * B < k + 1 / 2 := by
    by_contra! hb
    let t := ((k : ℝ) + 1 / 2) / w
    have ht : t ∈ Set.Icc A B := by
      dsimp [t]
      constructor
      · apply (le_div_iff₀ hw).mpr
        nlinarith
      · apply (div_le_iff₀ hw).mpr
        nlinarith
    have hc := hcover t ht
    have hwt : w * t = k + 1 / 2 := by dsimp [t]; field_simp
    rw [hwt, ndist_int_add, ndist_half] at hc
    linarith
  refine ⟨k, fun t ht => ?_⟩
  have hround : round (w * t) = k := by
    apply round_eq_iff.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hw.le,
      mul_le_mul_of_nonneg_left ht.2 hw.le]
  simpa only [ndist, hround] using hcover t ht

theorem single_band_length {A B w δ : ℝ} (hw : 0 < w) (hδ : δ < 1 / 2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (w * t) ≤ δ) :
    w * (B - A) ≤ 2 * δ := by
  obtain ⟨k, hk⟩ := single_band hw hδ hAB hcover
  have ha := abs_le.mp (hk A ⟨le_rfl, hAB⟩)
  have hb := abs_le.mp (hk B ⟨hAB, le_rfl⟩)
  nlinarith [ha.1, hb.2]

/-- In a two-speed covered interval, two distinct slow-speed bands cannot occur. -/
theorem no_two_slow_bands {A B p q δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p * t) ≤ δ ∨ ndist (q * t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hcu : |p * u - c| ≤ δ) (hdv : |p * v - d| ≤ δ) (hcd : c < d) : False := by
  have hcdR : (c : ℝ) + 1 ≤ d := by exact_mod_cast hcd
  have hcu' := abs_le.mp hcu
  have hdv' := abs_le.mp hdv
  let x := ((c : ℝ) + 3 * δ / 2) / p
  let y := ((c : ℝ) + 1 - 3 * δ / 2) / p
  have hpx : p * x = c + 3 * δ / 2 := by dsimp [x]; field_simp
  have hpy : p * y = c + 1 - 3 * δ / 2 := by dsimp [y]; field_simp
  have hux : u ≤ x := by nlinarith [hcu'.2]
  have hyv : y ≤ v := by nlinarith [hdv'.1]
  have hxy : x ≤ y := by nlinarith
  have hqcover : ∀ t ∈ Set.Icc x y, ndist (q * t) ≤ δ := by
    intro t ht
    have hpt : δ < ndist (p * t) := by
      apply strict_of_between (m := c) <;>
        nlinarith [mul_le_mul_of_nonneg_left ht.1 hp.le,
          mul_le_mul_of_nonneg_left ht.2 hp.le]
    exact (hcover t ⟨le_trans hu.1 (le_trans hux ht.1),
      le_trans ht.2 (le_trans hyv hv.2)⟩).resolve_left (not_le.mpr hpt)
  have hlen := single_band_length (lt_trans hp hpq) (by linarith) hxy hqcover
  have hlenp : p * (y - x) = 1 - 3 * δ := by linarith
  have hpos : 0 < y - x := by nlinarith
  have := mul_lt_mul_of_pos_right hpq hpos
  nlinarith

theorem slow_band_unique {A B p q δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p * t) ≤ δ ∨ ndist (q * t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hcu : |p * u - c| ≤ δ) (hdv : |p * v - d| ≤ δ) : c = d := by
  rcases lt_trichotomy c d with h | h | h
  · exact False.elim (no_two_slow_bands hp hpq hδ hsmall hcover hu hv hcu hdv h)
  · exact h
  · exact False.elim (no_two_slow_bands hp hpq hδ hsmall hcover hv hu hdv hcu h)







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

theorem fixed_slow_band {A B p q δ x : ℝ} {c : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hx : x ∈ Set.Icc A B) (hc : |p*x-c| ≤ δ) :
    ∀ t ∈ Set.Icc A B, |p*t-c| ≤ δ ∨ ndist (q*t) ≤ δ := by
  intro t ht
  rcases hcover t ht with hpbad | hqbad
  · left
    have heq := slow_band_unique hp hpq hδ hsmall hcover hx ht hc hpbad
    simpa only [ndist, ← heq] using hpbad
  · exact Or.inr hqbad









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
open LonelyRunner.BadCover

/-- A fast integer center which is slow-safe cannot have coverage beyond both
ends of its own bad band. -/
theorem solution {A B p q δ x : ℝ} {k : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5*δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hk : q*x = k) (hsafe : δ < ndist (p*x))
    (hleft : A < x-δ/q) (hright : x+δ/q < B) : False := by
  have hq := lt_trans hp hpq
  have hd : 0 < δ/q := div_pos hδ hq
  have hx : x ∈ Set.Icc A B := ⟨by linarith,by linarith⟩
  have hsmall' : 2*δ < 1 := by linarith
  have hk' : |q*x-k| ≤ δ := by rw [hk,sub_self,abs_zero]; exact hδ.le
  by_cases hex : ∃ u ∈ Set.Icc A B, ndist (p*u) ≤ δ
  · obtain ⟨u,hu,hpu⟩ := hex
    let c := round (p*u)
    have hc : |p*u-c| ≤ δ := hpu
    have hcov := fixed_slow_band hp hpq hδ hsmall hcover hu hc
    have hcx : ¬ |p*x-c| ≤ δ := fun h => (not_le.mpr hsafe) (le_trans (ndist_le_abs_sub _ c) h)
    rw [abs_le] at hcx
    push Not at hcx
    rcases lt_or_ge (p*x) ((c:ℝ)-δ) with hh | hh
    · have hqcov : ∀ t ∈ Set.Icc A x, ndist (q*t) ≤ δ := by
        intro t ht
        apply (hcov t ⟨ht.1,le_trans ht.2 hx.2⟩).resolve_left
        intro hb
        have := (abs_le.mp hb).1
        nlinarith [mul_le_mul_of_nonneg_left ht.2 hp.le]
      obtain ⟨j,hj⟩ := single_band hq (by linarith) hx.1 hqcov
      have hjk := band_center_unique hsmall' (hj x ⟨hx.1,le_rfl⟩) hk'
      have ha := (abs_le.mp (hj A ⟨le_rfl,hx.1⟩)).1
      rw [hjk] at ha
      have := mul_lt_mul_of_pos_left hleft hq
      rw [mul_sub,mul_div_cancel₀ _ hq.ne'] at this
      linarith
    · have hh' : (c:ℝ)+δ < p*x := by have := hcx (by linarith); linarith
      have hqcov : ∀ t ∈ Set.Icc x B, ndist (q*t) ≤ δ := by
        intro t ht
        apply (hcov t ⟨le_trans hx.1 ht.1,ht.2⟩).resolve_left
        intro hb
        have := (abs_le.mp hb).2
        nlinarith [mul_le_mul_of_nonneg_left ht.1 hp.le]
      obtain ⟨j,hj⟩ := single_band hq (by linarith) hx.2 hqcov
      have hjk := band_center_unique hsmall' (hj x ⟨le_rfl,hx.2⟩) hk'
      have hb := (abs_le.mp (hj B ⟨hx.2,le_rfl⟩)).2
      rw [hjk] at hb
      have := mul_lt_mul_of_pos_left hright hq
      rw [mul_add,mul_div_cancel₀ _ hq.ne'] at this
      linarith
  · have hqcov : ∀ t ∈ Set.Icc A B, ndist (q*t) ≤ δ := by
      intro t ht
      exact (hcover t ht).resolve_left (fun h => hex ⟨t,ht,h⟩)
    obtain ⟨j,hj⟩ := single_band hq (by linarith) (le_trans hx.1 hx.2) hqcov
    have hjk := band_center_unique hsmall' (hj x hx) hk'
    have ha := (abs_le.mp (hj A ⟨le_rfl,le_trans hx.1 hx.2⟩)).1
    rw [hjk] at ha
    have := mul_lt_mul_of_pos_left hleft hq
    rw [mul_sub,mul_div_cancel₀ _ hq.ne'] at this
    linarith
