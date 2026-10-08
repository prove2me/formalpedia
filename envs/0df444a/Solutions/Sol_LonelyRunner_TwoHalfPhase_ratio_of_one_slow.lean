-- Prove2me | solution 1 for LonelyRunner.TwoHalfPhase.ratio_of_one_slow
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:11:47.78955+00:00
-- url     : https://prove2.me/submissions/7d8863bd-5c98-40d7-8fea-47d0a18cba85

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

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

lemma triple_polynomial_pos {t : ℝ} (ht : 4 ≤ t) :
    0 < t^3-3*t^2-t-1 := by
  have hx : 0 ≤ t-4 := by linarith
  have hx2 := sq_nonneg (t-4)
  have hx3 := mul_nonneg hx2 hx
  nlinarith

lemma triple_denominator_pos {t : ℝ} (ht : 4 ≤ t) :
    0 < t^2-2*t-1 := by nlinarith [sq_nonneg (t-4)]

/-- The extremal three-band envelope is smaller than the square of the
single-band multiplicative stretch. -/
theorem half_phase_triple_ratio {t : ℝ} (ht : 4 ≤ t) :
    (t^2+1)/(t^2-2*t-1) ≤ ((t+1)/(t-1))^2 := by
  have hd := triple_denominator_pos ht
  have ht1 : 0 < t-1 := by linarith
  rw [div_pow]
  apply (div_le_div_iff₀ hd (sq_pos_of_pos ht1)).mpr
  nlinarith [triple_polynomial_pos ht]

/-- Positivity of the lower endpoint envelope in a genuine three-band chain. -/
theorem half_phase_envelope_pos {t T R : ℝ}
    (ht : 4 ≤ t) (hT : t ≤ T) (hR : t-1 ≤ R) :
    0 < T-1-2/R := by
  have hr : 0 < R := by linarith
  have hsmall : 2/R < 1 := (div_lt_one hr).mpr (by linarith)
  linarith

/-- Actual three-band endpoint envelopes imply the uniform ratio bound.
The hypotheses on R and T are the output of the interval-chain argument. -/
theorem half_phase_triple_envelope {t T R l h : ℝ}
    (ht : 4 ≤ t) (hT : t ≤ T) (hR : t-1 ≤ R)
    (hl : T-1-2/R ≤ l) (hh : h ≤ T+1+2/R) :
    h/l ≤ ((t+1)/(t-1))^2 := by
  have hr : 0 < R := by linarith
  have ht1 : 0 < t-1 := by linarith
  have hden := half_phase_envelope_pos ht hT hR
  have hlp : 0 < l := lt_of_lt_of_le hden hl
  have hden0 := half_phase_envelope_pos ht (le_refl t) (le_refl (t-1))
  have he : 2/R ≤ 2/(t-1) := by gcongr
  have hd : t-1-2/(t-1) ≤ T-1-2/R := by linarith
  have hTp : 0 < T := by linarith
  have hn : 0 ≤ T+1+2/R := by positivity
  have hfirst : h/l ≤ (T+1+2/R)/(T-1-2/R) := by
    exact div_le_div₀ hn hh hden hl
  have hrewrite : (T+1+2/R)/(T-1-2/R) =
      1+2*(1+2/R)/(T-1-2/R) := by
    apply (div_eq_iff hden.ne').mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hden.ne']
    ring
  have hrewrite0 : (t+1+2/(t-1))/(t-1-2/(t-1)) =
      1+2*(1+2/(t-1))/(t-1-2/(t-1)) := by
    apply (div_eq_iff hden0.ne').mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hden0.ne']
    ring
  have hmid : (T+1+2/R)/(T-1-2/R) ≤
      (t+1+2/(t-1))/(t-1-2/(t-1)) := by
    rw [hrewrite,hrewrite0]
    gcongr
  have heq : (t+1+2/(t-1))/(t-1-2/(t-1)) =
      (t^2+1)/(t^2-2*t-1) := by
    field_simp
    ring
  exact hfirst.trans (hmid.trans (heq ▸ half_phase_triple_ratio ht))













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

set_option maxHeartbeats 800000 in
/-- A cover involving one fixed slow band has the universal half-phase ratio.
The fast bands on either side are obtained from interval coverage, not supplied
as a certificate. -/
theorem solution {n p q A B u T : ℝ}
    (hn : 8 ≤ n) (hp : 0 < p) (hpq : p < q)
    (hA : 0 < A) (_hAB : A ≤ B) (hu : u ∈ Set.Icc A B)
    (hT : 1/2 ≤ T) (huT : |p*u-T| ≤ 1/n)
    (hcover : ∀z ∈ Set.Icc A B,
      |p*z-T| ≤ 1/n ∨ ndist (-1/2+q*z) ≤ 1/n) :
    B ≤ ((n+2)/(n-2))^2*A := by
  have hn0 : 0 < n := by linarith
  have hq : 0 < q := lt_trans hp hpq
  have hδ : 1/n < 1/2 := (div_lt_div_iff₀ hn0 (by norm_num : (0:ℝ)<2)).mpr (by linarith)
  have hδ0 : (0:ℝ) < 1/n := by positivity
  have hnδ : n*(1/n)=1 := by field_simp
  have htwo : 2/n=2*(1/n) := by ring
  let L := (T-1/n)/p
  let R := (T+1/n)/p
  let Z := (n+2)/(n-2)
  have hL : p*L=T-1/n := by dsimp [L]; field_simp
  have hR : p*R=T+1/n := by dsimp [R]; field_simp
  have hLp : 0 < L := by dsimp [L]; apply div_pos <;> linarith
  have hLR : L < R := by nlinarith
  have hLu : L ≤ u := by nlinarith [(abs_le.mp huT).1]
  have huR : u ≤ R := by nlinarith [(abs_le.mp huT).2]
  have hLband : |p*L-T| ≤ 1/n := by rw [hL]; simp [abs_of_pos hn0]
  have hRband : |p*R-T| ≤ 1/n := by rw [hR]; simp [abs_of_pos hn0]
  have hZR : R ≤ Z*L := single_band_stretch hn hp hT hLband hRband
  have hZ : 1 < Z := by
    dsimp [Z]
    exact (lt_div_iff₀ (by linarith : 0 < n-2)).mpr (by linarith)
  have hclosed : IsClosed {z : ℝ | ndist (-1/2+q*z) ≤ 1/n} :=
    isClosed_le (BadCover.continuous_ndist.comp
      (continuous_const.add (continuous_const.mul continuous_id))) continuous_const
  have left_lap (hAL : A < L) :
      ∃j : ℤ, ∀z ∈ Set.Icc A L, |(-1/2+q*z)-(j:ℝ)| ≤ 1/n := by
    have hsub : Set.Ico A L ⊆ {z : ℝ | ndist (-1/2+q*z) ≤ 1/n} := by
      intro z hz
      have hnot : ¬ |p*z-T| ≤ 1/n := by
        intro hh
        have hzp := mul_lt_mul_of_pos_left hz.2 hp
        linarith [(abs_le.mp hh).1]
      exact (hcover z ⟨hz.1, by linarith [hu.2,hz.2]⟩).resolve_left hnot
    have hc := closure_minimal hsub hclosed
    rw [closure_Ico hAL.ne] at hc
    exact ShiftedBlocks.single_band hq hδ hAL.le (fun z hz => hc hz)
  have right_lap (hRB : R < B) :
      ∃k : ℤ, ∀z ∈ Set.Icc R B, |(-1/2+q*z)-(k:ℝ)| ≤ 1/n := by
    have hsub : Set.Ioc R B ⊆ {z : ℝ | ndist (-1/2+q*z) ≤ 1/n} := by
      intro z hz
      have hnot : ¬ |p*z-T| ≤ 1/n := by
        intro hh
        have hzp := mul_lt_mul_of_pos_left hz.1 hp
        linarith [(abs_le.mp hh).2]
      exact (hcover z ⟨by linarith [hu.1,hz.1], hz.2⟩).resolve_left hnot
    have hc := closure_minimal hsub hclosed
    rw [closure_Ioc hRB.ne] at hc
    exact ShiftedBlocks.single_band hq hδ hRB.le (fun z hz => hc hz)
  by_cases hAL : A < L
  · obtain ⟨j,hj⟩ := left_lap hAL
    have hjA := hj A ⟨le_rfl,hAL.le⟩
    have hjL := hj L ⟨hAL.le,le_rfl⟩
    have hLA : L ≤ Z*A := lap_stretch hn hq hA hjA hjL
    by_cases hRB : R < B
    · obtain ⟨k,hk⟩ := right_lap hRB
      have hkR := hk R ⟨le_rfl,hRB.le⟩
      have hkB := hk B ⟨hRB.le,le_rfl⟩
      by_cases hjk : j=k
      · have hBA : B ≤ Z*A := lap_stretch hn hq hA (hjk ▸ hjA) hkB
        have hZZ : Z ≤ Z^2 := by nlinarith
        exact hBA.trans (mul_le_mul_of_nonneg_right hZZ hA.le)
      · have hjklt : j < k := by
          by_contra! hh
          have hkj : (k:ℝ)+1 ≤ j := by exact_mod_cast (show k+1 ≤ j by omega)
          have hqLR := mul_lt_mul_of_pos_left hLR hq
          linarith [(abs_le.mp hjL).1,(abs_le.mp hkR).2]
        have hjkR : (j:ℝ)+1 ≤ k := by exact_mod_cast hjklt
        have hgap : 1 ≤ q*(R-L)+2/n := by
          have ht := (abs_le.mp hjL).2
          have hb := (abs_le.mp hkR).1
          rw [htwo]
          nlinarith only [ht,hb,hjkR]
        have hlen : R-L=2/(n*p) := by dsimp [R,L]; field_simp; ring
        have hratio : n/2-1 ≤ q/p := by
          rw [hlen] at hgap
          apply (le_div_iff₀ hp).mpr
          have hh := mul_le_mul_of_nonneg_left hgap (mul_pos hn0 hp).le
          have he : n*p*(q*(2/(n*p))+2/n)=2*q+2*p := by field_simp
          rw [he] at hh
          nlinarith
        have hleft : q*(L-A) ≤ 2/n := by
          rw [htwo]
          nlinarith only [(abs_le.mp hjA).1,(abs_le.mp hjL).2]
        have hright : q*(B-R) ≤ 2/n := by
          rw [htwo]
          nlinarith only [(abs_le.mp hkR).1,(abs_le.mp hkB).2]
        have hleft' : L-2/(n*q) ≤ A := by
          apply (mul_le_mul_iff_right₀ hq).mp
          have he : q*(L-2/(n*q))=q*L-2/n := by field_simp
          rw [he]
          nlinarith
        have hright' : B ≤ R+2/(n*q) := by
          apply (mul_le_mul_iff_right₀ hq).mp
          have he : q*(R+2/(n*q))=q*R+2/n := by field_simp
          rw [he]
          nlinarith
        have hnp : 0 < n*p := mul_pos hn0 hp
        have hlow : n*T-1-2/(q/p) ≤ n*p*A := by
          have hh := mul_le_mul_of_nonneg_left hleft' hnp.le
          have he : n*p*(L-2/(n*q))=n*T-1-2/(q/p) := by
            dsimp [L]
            field_simp
          rwa [he] at hh
        have hhigh : n*p*B ≤ n*T+1+2/(q/p) := by
          have hh := mul_le_mul_of_nonneg_left hright' hnp.le
          have he : n*p*(R+2/(n*q))=n*T+1+2/(q/p) := by
            dsimp [R]
            field_simp
          rwa [he] at hh
        have hbound := half_phase_triple_envelope
          (t:=n/2) (T:=n*T) (R:=q/p) (l:=n*p*A) (h:=n*p*B)
          (by linarith) (by nlinarith) hratio hlow hhigh
        have hZZ : ((n/2+1)/(n/2-1))^2=Z^2 := by
          dsimp [Z]
          congr 1
          field_simp
        rw [hZZ] at hbound
        have heq : (n*p*B)/(n*p*A)=B/A := by field_simp
        rw [heq] at hbound
        exact (div_le_iff₀ hA).mp hbound
    · have hBR : B ≤ R := by linarith
      calc
        B ≤ R := hBR
        _ ≤ Z*L := hZR
        _ ≤ Z*(Z*A) := mul_le_mul_of_nonneg_left hLA (by linarith)
        _ = Z^2*A := by ring
  · have hLA : L ≤ A := by linarith
    by_cases hRB : R < B
    · obtain ⟨k,hk⟩ := right_lap hRB
      have hBR : B ≤ Z*R := lap_stretch hn hq (lt_trans hLp hLR)
        (hk R ⟨le_rfl,hRB.le⟩) (hk B ⟨hRB.le,le_rfl⟩)
      calc
        B ≤ Z*R := hBR
        _ ≤ Z*(Z*L) := mul_le_mul_of_nonneg_left hZR (by linarith)
        _ ≤ Z*(Z*A) := by gcongr
        _ = Z^2*A := by ring
    · have hBR : B ≤ R := by linarith
      have hZA : R ≤ Z*A := hZR.trans (mul_le_mul_of_nonneg_left hLA (by linarith))
      have hZZ : Z ≤ Z^2 := by nlinarith
      exact hBR.trans (hZA.trans (mul_le_mul_of_nonneg_right hZZ hA.le))
