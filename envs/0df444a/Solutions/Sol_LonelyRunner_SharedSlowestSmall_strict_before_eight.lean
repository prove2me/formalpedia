-- Prove2me | solution 1 for LonelyRunner.SharedSlowestSmall.strict_before_eight
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:13:45.808233+00:00
-- url     : https://prove2.me/submissions/5d5c5faa-11bd-4d15-a5e5-34c6c878bdef

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_ShiftedBlocks_length_le_of_one_slow

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm





theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x



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



theorem strict_of_between {x δ : ℝ} {m : ℤ}
    (hl : (m : ℝ) + δ < x) (hu : x < m + 1 - δ) : δ < ndist x := by
  change δ < |x - (round x : ℤ)|
  rcases le_or_gt (round x) m with h | h
  · have hR : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have hR : (m : ℝ) + 1 ≤ (round x : ℤ) := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)















end LonelyRunner.BadCover

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

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.FastestBoundary





























end LonelyRunner.FastestBoundary

namespace LonelyRunner.CollectiveBoundary























end LonelyRunner.CollectiveBoundary

namespace LonelyRunner.SharedFastest

open FastestBoundary















end LonelyRunner.SharedFastest

namespace LonelyRunner.CollectiveUnits







































end LonelyRunner.CollectiveUnits

namespace LonelyRunner.CollectiveFibreNormalForm





end LonelyRunner.CollectiveFibreNormalForm

namespace LonelyRunner.CollectiveFibreCounting
open CollectiveUnits











end LonelyRunner.CollectiveFibreCounting

namespace LonelyRunner.TotientCapacity









end LonelyRunner.TotientCapacity

namespace LonelyRunner.SmallTotient









end LonelyRunner.SmallTotient

namespace LonelyRunner.CollectiveFibreClassification
open CollectiveBoundary CollectiveUnits





















end LonelyRunner.CollectiveFibreClassification

namespace LonelyRunner.TwoBlockerGeometry



















end LonelyRunner.TwoBlockerGeometry

namespace LonelyRunner.SharedMiddleArithmetic





















end LonelyRunner.SharedMiddleArithmetic

namespace LonelyRunner.ShiftedWindows















end LonelyRunner.ShiftedWindows

namespace LonelyRunner.ShiftedBlocks

theorem single_band {A B w β δ : ℝ} (hw : 0 < w) (hδ : δ < 1/2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (β+w*t) ≤ δ) :
    ∃ k : ℤ, ∀ t ∈ Set.Icc A B, |β+w*t-k| ≤ δ := by
  let k : ℤ := round (β+w*A)
  have hA : |β+w*A-k| ≤ δ := hcover A ⟨le_rfl,hAB⟩
  have hAl := (abs_le.mp hA).1
  have hAu := (abs_le.mp hA).2
  have hB : β+w*B < k+1/2 := by
    by_contra! hb
    let t := ((k:ℝ)+1/2-β)/w
    have ht : t ∈ Set.Icc A B := by
      dsimp [t]
      constructor
      · apply (le_div_iff₀ hw).2; linarith
      · apply (div_le_iff₀ hw).2; linarith
    have hc := hcover t ht
    have heq : β+w*t=k+1/2 := by dsimp [t]; field_simp; ring
    rw [heq,ndist_int_add,ndist_half] at hc
    linarith
  refine ⟨k,fun t ht => ?_⟩
  have heq : round (β+w*t)=k := by
    apply round_eq_iff.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hw.le,
      mul_le_mul_of_nonneg_left ht.2 hw.le]
  simpa only [ndist,heq] using hcover t ht

theorem single_band_length {A B w β δ : ℝ} (hw : 0 < w) (hδ : δ < 1/2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (β+w*t) ≤ δ) :
    w*(B-A) ≤ 2*δ := by
  obtain ⟨k,hk⟩ := single_band hw hδ hAB hcover
  have ha := abs_le.mp (hk A ⟨le_rfl,hAB⟩)
  have hb := abs_le.mp (hk B ⟨hAB,le_rfl⟩)
  nlinarith [ha.1,hb.2]

theorem no_two_slow_bands {A B p q α β δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : δ < 1/2)
    (hbridge : 2*δ*p < (1-2*δ)*q)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (α+p*t) ≤ δ ∨ ndist (β+q*t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hc : |α+p*u-c| ≤ δ) (hd : |α+p*v-d| ≤ δ) (hcd : c < d) : False := by
  have hcdR : (c:ℝ)+1 ≤ d := by exact_mod_cast hcd
  let x := ((c:ℝ)+δ-α)/p
  let y := ((c:ℝ)+1-δ-α)/p
  have hpx : p*x=(c:ℝ)+δ-α := by dsimp [x]; field_simp
  have hpy : p*y=(c:ℝ)+1-δ-α := by dsimp [y]; field_simp
  have hux : u ≤ x := by nlinarith [(abs_le.mp hc).2]
  have hyv : y ≤ v := by nlinarith [(abs_le.mp hd).1]
  have hxy : x < y := by nlinarith
  have hsub : Set.Ioo x y ⊆ {t : ℝ | ndist (β+q*t) ≤ δ} := by
    intro t ht
    have hsafe : δ < ndist (α+p*t) := by
      apply BadCover.strict_of_between (m := c) <;>
        nlinarith [mul_lt_mul_of_pos_left ht.1 hp,mul_lt_mul_of_pos_left ht.2 hp]
    exact (hcover t ⟨by linarith [hu.1,ht.1],by linarith [hv.2,ht.2]⟩).resolve_left
      (not_le.mpr hsafe)
  have hclosed : IsClosed {t : ℝ | ndist (β+q*t) ≤ δ} :=
    isClosed_le (BadCover.continuous_ndist.comp
      (continuous_const.add (continuous_const.mul continuous_id))) continuous_const
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo hxy.ne] at hcl
  have hlen := single_band_length hq hδ hxy.le (fun t ht => hcl ht)
  have hmul := mul_le_mul_of_nonneg_left hlen hp.le
  nlinarith [congrArg (fun z : ℝ => q*z) hpx,congrArg (fun z : ℝ => q*z) hpy]

theorem slow_band_unique {A B p q α β δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : δ < 1/2)
    (hbridge : 2*δ*p < (1-2*δ)*q)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (α+p*t) ≤ δ ∨ ndist (β+q*t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hc : |α+p*u-c| ≤ δ) (hd : |α+p*v-d| ≤ δ) : c=d := by
  rcases lt_trichotomy c d with h | h | h
  · exact False.elim (no_two_slow_bands hp hq hδ hbridge hcover hu hv hc hd h)
  · exact h
  · exact False.elim (no_two_slow_bands hp hq hδ hbridge hcover hv hu hd hc h)





/-- Exact phase-uniform upper bound for any fully blocked closed interval. -/
theorem covered_length_le {A B p q α β δ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ : δ < 1/2)
    (hbridge : 2*δ*p < (1-2*δ)*q) (hAB : A ≤ B)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (α+p*t) ≤ δ ∨ ndist (β+q*t) ≤ δ) :
    B-A ≤ blockBound p q δ := by
  by_cases hex : ∃ u ∈ Set.Icc A B, ndist (α+p*u) ≤ δ
  · obtain ⟨u,hu,hcu⟩ := hex
    let c : ℤ := round (α+p*u)
    have hc : |α+p*u-c| ≤ δ := hcu
    apply length_le_of_one_slow hp hq hδ0 hδ hu hc
    intro t ht
    rcases hcover t ht with hh | hh
    · left
      have heq := slow_band_unique hp hq hδ hbridge hcover hu ht hc
        (show |α+p*t-round (α+p*t)| ≤ δ from hh)
      simpa only [← heq] using (show |α+p*t-round (α+p*t)| ≤ δ from hh)
    · exact Or.inr hh
  · have hqcover (t : ℝ) (ht : t ∈ Set.Icc A B) : ndist (β+q*t) ≤ δ := by
      exact (hcover t ht).resolve_left (fun hh => hex ⟨t,ht,hh⟩)
    have hlen := single_band_length hq hδ hAB hqcover
    have hlen' : B-A ≤ 2*δ/q := (le_div_iff₀ hq).2 (by nlinarith)
    have ha : 0 ≤ 2*δ/p := by positivity
    exact le_trans (show B-A ≤ 2*δ/p+2*δ/q by linarith) (le_max_left _ _)

/-- A sufficiently long window works for completely arbitrary starting phases. -/
theorem strict_of_length_gt {A B p q α β δ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ : δ < 1/2)
    (hbridge : 2*δ*p < (1-2*δ)*q) (hAB : A ≤ B)
    (hlen : blockBound p q δ < B-A) : ShiftedWindows.StrictWindow p q α β δ A B := by
  by_contra hh
  have hcover : ∀ t ∈ Set.Icc A B, ndist (α+p*t) ≤ δ ∨ ndist (β+q*t) ≤ δ := by
    intro t ht
    by_contra h
    push Not at h
    exact hh ⟨t,ht,h.1,h.2⟩
  exact (not_le.mpr hlen) (covered_length_le hp hq hδ0 hδ hbridge hAB hcover)





end LonelyRunner.ShiftedBlocks

namespace LonelyRunner.WholeFlankWindows

open BadCover SeparatedMulti











end LonelyRunner.WholeFlankWindows

namespace LonelyRunner.CollectivePhase







end LonelyRunner.CollectivePhase

namespace LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits







end LonelyRunner.CollectiveBoundaryForcing

namespace LonelyRunner.CollectiveSecondFastest

open BadCover



















end LonelyRunner.CollectiveSecondFastest

namespace LonelyRunner.SmallFibrePhase
open CollectiveFibreNormalForm CollectiveSecondFastest

















end LonelyRunner.SmallFibrePhase

namespace LonelyRunner.PrimitiveFibre
open CollectiveUnits CollectiveFibreNormalForm

















end LonelyRunner.PrimitiveFibre

namespace LonelyRunner.CanonicalTwoCover
open CollectiveUnits CollectiveBoundary CollectiveFibreClassification





end LonelyRunner.CanonicalTwoCover

namespace LonelyRunner.RealClockCapacity
open CollectiveBoundary CollectiveUnits CollectiveSecondFastest

























end LonelyRunner.RealClockCapacity

namespace LonelyRunner.TwoBlockerArithmetic
open CollectiveUnits























end LonelyRunner.TwoBlockerArithmetic

namespace LonelyRunner.TwoHalfPhase

open TwoBlockerArithmetic













end LonelyRunner.TwoHalfPhase

namespace LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover







end LonelyRunner.SharedSlowestHalf

namespace LonelyRunner.ComplementaryEscape
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm









end LonelyRunner.ComplementaryEscape

namespace LonelyRunner.SmallFibreTable
open CollectiveUnits CollectiveFibreNormalForm

























end LonelyRunner.SmallFibreTable

namespace LonelyRunner.SharedSlowestSmall
open CollectiveSecondFastest





end LonelyRunner.SharedSlowestSmall

namespace LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm





end LonelyRunner.SharedSlowest

namespace LonelyRunner.UniqueSharedRepair







end LonelyRunner.UniqueSharedRepair

open LonelyRunner
open LonelyRunner.SharedSlowestSmall
open CollectiveSecondFastest

/-- Two arbitrarily phased faster runners have a strict clock before eight.
A coarse classical interval-length bound suffices for the small exception. -/
theorem solution {n slow fast theta phi : ℝ}
    (hn : 5 ≤ n) (hs : 1 < slow) (horder : slow < fast) :
    ∃z ∈ Set.Ioo 1 8, 1/n < ndist (theta-slow*z/n) ∧
      1/n < ndist (phi-fast*z/n) := by
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < slow := by linarith
  have hf0 : 0 < fast := by linarith
  let p := slow/n
  let q := fast/n
  let δ := 1/n
  have hp : 0 < p := div_pos hs0 hn0
  have hq : 0 < q := div_pos hf0 hn0
  have hpq : p < q := div_lt_div_of_pos_right horder hn0
  have hδ : δ < 1/2 := by
    dsimp [δ]
    apply (div_lt_div_iff₀ hn0 (by norm_num : (0:ℝ) < 2)).mpr
    linarith
  have hbridge : 2*δ*p < (1-2*δ)*q := by
    apply (mul_lt_mul_iff_right₀ hn0).mp
    have h₁ : n*(2*δ*p)=2*p := by dsimp [δ]; field_simp
    have h₂ : n*((1-2*δ)*q)=(n-2)*q := by dsimp [δ]; field_simp
    rw [h₁,h₂]
    nlinarith [mul_nonneg (show 0 ≤ n-4 by linarith) hq.le]
  have ha : 2*δ/p < 2 := by
    have he : 2*δ/p=2/slow := by dsimp [δ,p]; field_simp
    rw [he]
    exact (div_lt_iff₀ hs0).mpr (by linarith)
  have hb : 2*δ/q < 2 := by
    have he : 2*δ/q=2/fast := by dsimp [δ,q]; field_simp
    rw [he]
    exact (div_lt_iff₀ hf0).mpr (by linarith)
  have hbound : ShiftedBlocks.blockBound p q δ < 6 := by
    unfold ShiftedBlocks.blockBound
    apply max_lt
    · linarith
    · apply (div_lt_iff₀ hq).mpr
      have hfloor := Int.floor_le (q*(2*δ/p+2*δ/q))
      have hh : q*(2*δ/p+2*δ/q)+2*δ=q*(2*δ/p+2*(2*δ/q)) := by field_simp; ring
      have ht := mul_lt_mul_of_pos_left (show 2*δ/p+2*(2*δ/q) < 6 by linarith) hq
      nlinarith only [hfloor,hh,ht]
  obtain ⟨z,hz,hzs,hzf⟩ := ShiftedBlocks.strict_of_length_gt
    (A:=(3:ℝ)/2) (B:=(15:ℝ)/2) (α:=-theta) (β:=-phi)
    hp hq (by dsimp [δ]; positivity) hδ hbridge (by norm_num) (by linarith)
  refine ⟨z,⟨by linarith [hz.1],by linarith [hz.2]⟩,?_,?_⟩
  · have he : -theta+p*z=-(theta-slow*z/n) := by dsimp [p]; ring
    simpa only [he,ndist_neg] using hzs
  · have he : -phi+q*z=-(phi-fast*z/n) := by dsimp [q]; ring
    simpa only [he,ndist_neg] using hzf
