-- Prove2me | solution 1 for LonelyRunner.BadCover.slow_center_gap
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:55:07.142703+00:00
-- url     : https://prove2.me/submissions/02150058-e2b3-44ef-aa03-f9d4f8731e09

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm





theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m

@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]



@[simp] theorem ndist_neg (x : ℝ) : ndist (-x) = ndist x := by
  rw [ndist_eq_norm, ndist_eq_norm, AddCircle.coe_neg, norm_neg]







/-- On `[0, 1/2]` the distance to the nearest integer is the identity. -/
theorem ndist_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ndist x = x := by
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨h0, by linarith⟩
  rw [ndist_eq_min_fract, hfr]
  exact min_eq_left (by linarith)

@[simp] theorem ndist_half : ndist (1 / 2) = 1 / 2 := ndist_of_mem (by norm_num) le_rfl

















end LonelyRunner

namespace LonelyRunner.BadCover

theorem continuous_ndist : Continuous ndist := by
  have heq : ndist = fun x : ℝ => ‖(x : UnitAddCircle)‖ := funext ndist_eq_norm
  rw [heq]
  exact continuous_norm.comp (AddCircle.continuous_mk' (1 : ℝ))

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

/-- A fast band containing the left endpoint meets the unique slow band. -/
theorem left_overlap {A B p q δ x : ℝ} {c k : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ) (hsmall : 2 * δ < 1)
    (hx : x ∈ Set.Icc A B) (hc : |p * x - c| ≤ δ)
    (hk : |q * A - k| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |p * t - c| ≤ δ ∨ ndist (q * t) ≤ δ) :
    ∃ t : ℝ, |p * t - c| ≤ δ ∧ |q * t - k| ≤ δ := by
  by_cases ha : |p * A - c| ≤ δ
  · exact ⟨A, ha, hk⟩
  let L := ((c : ℝ) - δ) / p
  have hpL : p * L = c - δ := by dsimp [L]; field_simp
  have hcx := abs_le.mp hc
  have hAL : A < L := by
    have hpa : p * A < c - δ := by
      have := mul_le_mul_of_nonneg_left hx.1 hp.le
      rw [abs_le] at ha
      push Not at ha
      rcases lt_or_ge (p * A) (c - δ) with hh | hh
      · exact hh
      · exact False.elim (by linarith [ha (by linarith), hcx.2])
    nlinarith
  have hLx : L ≤ x := by nlinarith [hcx.1]
  have hsub : Set.Ico A L ⊆ {t : ℝ | ndist (q * t) ≤ δ} := by
    intro t ht
    have hpt : ¬ |p * t - c| ≤ δ := by
      intro hh
      have := (abs_le.mp hh).1
      nlinarith [mul_lt_mul_of_pos_left ht.2 hp]
    exact (hcover t ⟨ht.1, le_trans ht.2.le (le_trans hLx hx.2)⟩).resolve_left hpt
  have hclosed : IsClosed {t : ℝ | ndist (q * t) ≤ δ} :=
    isClosed_le (continuous_ndist.comp (continuous_const.mul continuous_id)) continuous_const
  have hsub' := closure_minimal hsub hclosed
  rw [closure_Ico (ne_of_lt hAL)] at hsub'
  obtain ⟨j, hj⟩ := single_band hq (by linarith) hAL.le hsub'
  have hjk : j = k := band_center_unique hsmall (hj A ⟨le_rfl, hAL.le⟩) hk
  refine ⟨L, ?_, ?_⟩
  · rw [hpL, sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
  · simpa [hjk] using hj L ⟨hAL.le, le_rfl⟩

/-- The right-endpoint version follows by reflecting time. -/
theorem right_overlap {A B p q δ x : ℝ} {c k : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ) (hsmall : 2 * δ < 1)
    (hx : x ∈ Set.Icc A B) (hc : |p * x - c| ≤ δ)
    (hk : |q * B - k| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |p * t - c| ≤ δ ∨ ndist (q * t) ≤ δ) :
    ∃ t : ℝ, |p * t - c| ≤ δ ∧ |q * t - k| ≤ δ := by
  have hneg (w t : ℝ) (j : ℤ) : |w * (-t) - (-j : ℤ)| = |w * t - j| := by
    rw [Int.cast_neg, show w * (-t) - -(j : ℝ) = -(w * t - j) by ring, abs_neg]
  have hc' : |p * (-x) - (-c : ℤ)| ≤ δ := by simpa only [hneg] using hc
  have hk' : |q * (-B) - (-k : ℤ)| ≤ δ := by simpa only [hneg] using hk
  have hcover' : ∀ t ∈ Set.Icc (-B) (-A),
      |p * t - (-c : ℤ)| ≤ δ ∨ ndist (q * t) ≤ δ := by
    intro t ht
    have hh := hcover (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [mul_neg, ndist_neg, ← hneg p t (-c), neg_neg] using hh
  obtain ⟨t, ht1, ht2⟩ := left_overlap hp hq hδ hsmall
    (show -x ∈ Set.Icc (-B) (-A) from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    hc' hk' hcover'
  refine ⟨-t, ?_, ?_⟩
  · simpa only [← hneg p t (-c), neg_neg] using ht1
  · simpa only [← hneg q t (-k), neg_neg] using ht2



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

/-- Crossing a slow band on both sides of a fast-safe center forces a lower
bound on the ratio of the two speeds. -/
theorem solution {A B p q δ x : ℝ} {c : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5*δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hc : p*x = c) (hsafe : δ < ndist (q*x))
    (hleft : A < x-δ/p) (hright : x+δ/p < B) :
    (1-2*δ)*p ≤ 2*δ*q := by
  have hq := lt_trans hp hpq
  have hd : 0 < δ/p := div_pos hδ hp
  have hx : x ∈ Set.Icc A B := ⟨by linarith,by linarith⟩
  have hc' : |p*x-c| ≤ δ := by rw [hc,sub_self,abs_zero]; exact hδ.le
  have hcov := fixed_slow_band hp hpq hδ hsmall hcover hx hc'
  have hsmall' : 2*δ < 1 := by linarith
  have ha : ndist (q*A) ≤ δ := by
    apply (hcov A ⟨le_rfl,le_trans hx.1 hx.2⟩).resolve_left
    intro hh
    have := (abs_le.mp hh).1
    have := mul_lt_mul_of_pos_left hleft hp
    rw [mul_sub, mul_div_cancel₀ _ hp.ne'] at this
    linarith
  have hb : ndist (q*B) ≤ δ := by
    apply (hcov B ⟨le_trans hx.1 hx.2,le_rfl⟩).resolve_left
    intro hh
    have := (abs_le.mp hh).2
    have := mul_lt_mul_of_pos_left hright hp
    rw [mul_add, mul_div_cancel₀ _ hp.ne'] at this
    linarith
  let k := round (q*A)
  let j := round (q*B)
  have hak : |q*A-k| ≤ δ := ha
  have hbj : |q*B-j| ≤ δ := hb
  have hkx : (k:ℝ)+δ < q*x := by
    have h := abs_le.mp hak
    have hx' := mul_le_mul_of_nonneg_left hx.1 hq.le
    by_contra! hh
    have : ndist (q*x) ≤ δ := le_trans (ndist_le_abs_sub _ k) (abs_le.mpr ⟨by linarith,by linarith⟩)
    linarith
  have hxj : q*x < (j:ℝ)-δ := by
    have h := abs_le.mp hbj
    have hx' := mul_le_mul_of_nonneg_left hx.2 hq.le
    by_contra! hh
    have : ndist (q*x) ≤ δ := le_trans (ndist_le_abs_sub _ j) (abs_le.mpr ⟨by linarith,by linarith⟩)
    linarith
  have hkjR : (k:ℝ) < j := by linarith
  have hkj : k < j := by exact_mod_cast hkjR
  have hstep : (k:ℝ)+1 ≤ j := by exact_mod_cast hkj
  obtain ⟨u,hu,huk⟩ := left_overlap hp hq hδ hsmall' hx hc' hak hcov
  obtain ⟨v,hv,hvj⟩ := right_overlap hp hq hδ hsmall' hx hc' hbj hcov
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have huk' := abs_le.mp huk
  have hvj' := abs_le.mp hvj
  have hgap : 1-2*δ ≤ q*(v-u) := by linarith [huk'.2,hvj'.1]
  have hlen : p*(v-u) ≤ 2*δ := by linarith [hu'.1,hv'.2]
  nlinarith [mul_le_mul_of_nonneg_right hgap hp.le,
    mul_le_mul_of_nonneg_right hlen hq.le]
