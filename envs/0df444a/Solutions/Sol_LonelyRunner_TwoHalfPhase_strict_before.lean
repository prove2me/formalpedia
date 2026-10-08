-- Prove2me | solution 1 for LonelyRunner.TwoHalfPhase.strict_before
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:18:41.06498+00:00
-- url     : https://prove2.me/submissions/9735de62-f49c-4b15-8f23-b2d197c75be5

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_TwoHalfPhase_ratio_of_one_slow

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

/-- A bad half-phase lap at positive time has a nonnegative integer index. -/
theorem lap_nonnegative {n p x : ℝ} {c : ℤ}
    (hn : 8 ≤ n) (hp : 0 < p) (hx : 0 < x)
    (hc : |(-1/2+p*x)-(c:ℝ)| ≤ 1/n) : 0 ≤ c := by
  have hn0 : 0 < n := by linarith
  have hd : 1/n < 1/2 := (div_lt_div_iff₀ hn0 (by norm_num : (0:ℝ)<2)).mpr (by linarith)
  by_contra! hh
  have hcR : (c:ℝ) ≤ -1 := by exact_mod_cast (show c ≤ -1 by omega)
  nlinarith [mul_pos hp hx, (abs_le.mp hc).2]

/-- Any two positive points in one half-phase band have stretch at most Z. -/
theorem single_band_stretch {n p x y T : ℝ}
    (hn : 8 ≤ n) (hp : 0 < p) (hT : 1/2 ≤ T)
    (hx : |p*x-T| ≤ 1/n) (hy : |p*y-T| ≤ 1/n) :
    y ≤ ((n+2)/(n-2))*x := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n-2 := by linarith
  have hnδ : n*(1/n)=1 := by field_simp
  have hlo := (abs_le.mp hx).1
  have hhi := (abs_le.mp hy).2
  have hmlo := mul_le_mul_of_nonneg_left (show T-1/n ≤ p*x by linarith)
    (show 0 ≤ n+2 by linarith)
  have hmhi := mul_le_mul_of_nonneg_left (show p*y ≤ T+1/n by linarith) hd.le
  have hh : p*((n-2)*y) ≤ p*((n+2)*x) := by nlinarith
  have hh' := (mul_le_mul_iff_right₀ hp).mp hh
  apply (mul_le_mul_iff_right₀ hd).mp
  have heq : (n-2)*(((n+2)/(n-2))*x)=(n+2)*x := by field_simp
  rw [heq]
  exact hh'

/-- The same stretch estimate in the integer-lap notation of the covering tools. -/
theorem lap_stretch {n p x y : ℝ} {c : ℤ}
    (hn : 8 ≤ n) (hp : 0 < p) (hx0 : 0 < x)
    (hx : |(-1/2+p*x)-(c:ℝ)| ≤ 1/n)
    (hy : |(-1/2+p*y)-(c:ℝ)| ≤ 1/n) :
    y ≤ ((n+2)/(n-2))*x := by
  have hc := lap_nonnegative hn hp hx0 hx
  have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc
  apply single_band_stretch hn hp (show (1:ℝ)/2 ≤ (c:ℝ)+1/2 by linarith)
  · convert hx using 1; congr 1; ring
  · convert hy using 1; congr 1; ring



/-- Every positive interval covered by two half-phase bad sets has endpoint
ratio at most the square of the single-band stretch. This derives the unique
slow band and the full interval decomposition from the cover itself. -/
theorem covered_ratio {n p q A B : ℝ}
    (hn : 8 ≤ n) (hp : 0 < p) (hpq : p < q)
    (hA : 0 < A) (hAB : A ≤ B)
    (hcover : ∀z ∈ Set.Icc A B,
      ndist (-1/2+p*z) ≤ 1/n ∨ ndist (-1/2+q*z) ≤ 1/n) :
    B ≤ ((n+2)/(n-2))^2*A := by
  have hn0 : 0 < n := by linarith
  have hq : 0 < q := lt_trans hp hpq
  have hδ : 1/n < 1/2 := (div_lt_div_iff₀ hn0 (by norm_num : (0:ℝ)<2)).mpr (by linarith)
  have hbridge : 2*(1/n)*p < (1-2*(1/n))*q := by
    apply (mul_lt_mul_iff_right₀ hn0).mp
    have he₁ : n*(2*(1/n)*p)=2*p := by field_simp
    have he₂ : n*((1-2*(1/n))*q)=(n-2)*q := by field_simp
    rw [he₁,he₂]
    nlinarith [mul_nonneg (show 0 ≤ n-4 by linarith) hq.le]
  by_cases hex : ∃u ∈ Set.Icc A B, ndist (-1/2+p*u) ≤ 1/n
  · obtain ⟨u,hu,hbad⟩ := hex
    let c : ℤ := round (-1/2+p*u)
    have hc : |(-1/2+p*u)-(c:ℝ)| ≤ 1/n := hbad
    have hc0 := lap_nonnegative hn hp (lt_of_lt_of_le hA hu.1) hc
    have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc0
    apply ratio_of_one_slow hn hp hpq hA hAB hu
      (show (1:ℝ)/2 ≤ (c:ℝ)+1/2 by linarith)
    · convert hc using 1; congr 1; ring
    · intro z hz
      rcases hcover z hz with hpbad | hqbad
      · left
        have heq := ShiftedBlocks.slow_band_unique hp hq hδ hbridge hcover hu hz hc
          (show |(-1/2+p*z)-(round (-1/2+p*z):ℤ)| ≤ 1/n from hpbad)
        have hh : |(-1/2+p*z)-(c:ℝ)| ≤ 1/n := by
          simpa only [← heq] using
            (show |(-1/2+p*z)-(round (-1/2+p*z):ℤ)| ≤ 1/n from hpbad)
        convert hh using 1; congr 1; ring
      · exact Or.inr hqbad
  · have hf : ∀z ∈ Set.Icc A B, ndist (-1/2+q*z) ≤ 1/n := by
      intro z hz
      exact (hcover z hz).resolve_left (fun hb => hex ⟨z,hz,hb⟩)
    obtain ⟨c,hc⟩ := ShiftedBlocks.single_band hq hδ hAB hf
    have hh := lap_stretch hn hq hA (hc A ⟨le_rfl,hAB⟩) (hc B ⟨hAB,le_rfl⟩)
    have hZ : 1 < (n+2)/(n-2) :=
      (lt_div_iff₀ (by linarith : 0 < n-2)).mpr (by linarith)
    have hZZ : (n+2)/(n-2) ≤ ((n+2)/(n-2))^2 := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hZZ hA.le)



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
open LonelyRunner.TwoHalfPhase
open TwoBlockerArithmetic

/-- With any open upper bound beyond Z², two half-phase runners have an
actual strictly safe clock between 1 and that bound. No band-chain or
component certificate is assumed. -/
theorem solution {n slow fast L : ℝ}
    (hn : 10 ≤ n) (hslow : 0 < slow) (horder : slow < fast)
    (hL : ((n+2)/(n-2))^2 < L) :
    ∃z ∈ Set.Ioo 1 L,
      1/n < ndist (1/2-slow*z/n) ∧ 1/n < ndist (1/2-fast*z/n) := by
  have hn0 : 0 < n := by linarith
  have hfast : 0 < fast := lt_trans hslow horder
  have hZ : 1 < (n+2)/(n-2) :=
    (lt_div_iff₀ (by linarith : 0 < n-2)).mpr (by linarith)
  have h1L : 1 < L := by nlinarith
  by_contra! hno
  have hneg (v z : ℝ) : -1/2+(v/n)*z=-(1/2-v*z/n) := by ring
  have hcover : Set.Ioo 1 L ⊆ {z : ℝ |
      ndist (-1/2+(slow/n)*z) ≤ 1/n ∨ ndist (-1/2+(fast/n)*z) ≤ 1/n} := by
    intro z hz
    change ndist (-1/2+(slow/n)*z) ≤ 1/n ∨ ndist (-1/2+(fast/n)*z) ≤ 1/n
    rw [hneg,hneg,ndist_neg,ndist_neg]
    by_cases hs : ndist (1/2-slow*z/n) ≤ 1/n
    · exact Or.inl hs
    · exact Or.inr (hno z hz (lt_of_not_ge hs))
  have hclosed : IsClosed {z : ℝ |
      ndist (-1/2+(slow/n)*z) ≤ 1/n ∨ ndist (-1/2+(fast/n)*z) ≤ 1/n} := by
    apply IsClosed.union <;>
      exact isClosed_le (BadCover.continuous_ndist.comp
        (continuous_const.add (continuous_const.mul continuous_id))) continuous_const
  have hc := closure_minimal hcover hclosed
  rw [closure_Ioo h1L.ne] at hc
  have hh := covered_ratio (n:=n) (p:=slow/n) (q:=fast/n) (A:=1) (B:=L)
    (by linarith) (div_pos hslow hn0)
    (div_lt_div_of_pos_right horder hn0) (by norm_num) h1L.le
    (fun z hz => hc hz)
  nlinarith
