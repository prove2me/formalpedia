-- Prove2me | solution 1 for LonelyRunner.CollectiveSecondFastest.strict_of_half_phase_band
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:13:23.563736+00:00
-- url     : https://prove2.me/submissions/2e364d15-6180-42cd-b45e-f4df14226108

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_CollectiveSecondFastest_clock_exit_escape
import Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















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





















@[simp] theorem mem_primitiveFlanks {n r b : ℕ} :
    b ∈ primitiveFlanks n r ↔ n-r ≤ b ∧ b < n ∧ Nat.Coprime r b := by
  simp [primitiveFlanks, and_assoc]

@[simp] theorem card_primitiveFlanks {n r : ℕ} (hrn : r ≤ n) :
    (primitiveFlanks n r).card = r.totient := by
  have heq : n-r+r=n := Nat.sub_add_cancel hrn
  simpa [primitiveFlanks, heq] using Nat.filter_coprime_Ico_eq_totient r (n-r)

/-- Reduction modulo `r` is injective on one period. -/
theorem primitiveFlanks_mod_injective {n r b c : ℕ}
    (hb : b ∈ primitiveFlanks n r) (hc : c ∈ primitiveFlanks n r)
    (heq : b%r=c%r) : b=c := by
  obtain ⟨hbl,hbu,_⟩ := mem_primitiveFlanks.mp hb
  obtain ⟨hcl,hcu,_⟩ := mem_primitiveFlanks.mp hc
  exact Nat.ModEq.eq_of_abs_lt heq (by rw [abs_lt]; omega)

/-- If the modulus is even, at most one primitive representative is discarded
by imposing the terminal margin `b ≤ n-3`. -/
theorem terminal_discard_card {n r : ℕ} (heven : Even r) :
    ((primitiveFlanks n r).filter (fun b => n-3 < b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb c hc
  obtain ⟨hb, hbt⟩ := Finset.mem_filter.mp hb
  obtain ⟨hc, hct⟩ := Finset.mem_filter.mp hc
  obtain ⟨hbl, hbu, hbc⟩ := mem_primitiveFlanks.mp hb
  obtain ⟨hcl, hcu, hcc⟩ := mem_primitiveFlanks.mp hc
  have hbodd : Odd b := Nat.coprime_two_left.mp (hbc.of_dvd_left heven.two_dvd)
  have hcodd : Odd c := Nat.coprime_two_left.mp (hcc.of_dvd_left heven.two_dvd)
  have hbmod := Nat.odd_iff.mp hbodd
  have hcmod := Nat.odd_iff.mp hcodd
  omega

/-- The surviving exit flanks have cardinality at least `phi(r)-1`. -/
theorem terminal_survivor_card {n r : ℕ} (hrn : r ≤ n) (heven : Even r) :
    r.totient ≤ ((primitiveFlanks n r).filter (fun b => b ≤ n-3)).card + 1 := by
  have hh := terminal_discard_card (n:=n) heven
  have hs := Finset.card_filter_add_card_filter_not
    (s:=primitiveFlanks n r) (p:=fun b => b ≤ n-3)
  simp only [not_le, card_primitiveFlanks hrn] at hs
  omega

/-- An elementary capacity bound for any finite family of covering sets. -/
theorem cover_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (W : Finset β) (B : β → Finset α) (capacity : ℕ)
    (hcover : ∀ x ∈ X, ∃ q ∈ W, x ∈ B q)
    (hcap : ∀ q ∈ W, (B q).card ≤ capacity) :
    X.card ≤ W.card * capacity := by
  have hsub : X ⊆ W.biUnion B := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨q, hq, hqx⟩
  calc
    X.card ≤ (W.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ W, (B q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ W, capacity := Finset.sum_le_sum hcap
    _ = W.card * capacity := by simp



/-- Divisibility formulation of injectivity on a primitive period. -/
theorem primitiveFlanks_eq_of_dvd {n r b c : ℕ}
    (hb : b ∈ primitiveFlanks n r) (hc : c ∈ primitiveFlanks n r)
    (hd : (r:ℤ) ∣ (b:ℤ)-c) : b=c := by
  apply primitiveFlanks_mod_injective hb hc
  exact (Nat.modEq_iff_dvd.mpr hd).symm



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



/-- A half-phase band covering the canonical boundary exits at most at this clock value. -/
theorem half_phase_exit_bound {n T gamma : ℝ}
    (hn : 2 < n) (hT : n/2 ≤ T) (hg : 0 < gamma)
    (hband : |gamma-T| ≤ 1) :
    1 ≤ (T+1)/gamma ∧ (T+1)/gamma ≤ (n+2)/(n-2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hband
  constructor
  · exact (le_div_iff₀ hg).mpr (by linarith)
  · apply (div_le_div_iff₀ hg (by linarith : 0 < n-2)).mpr
    nlinarith [mul_nonneg (show 0 ≤ gamma-(T-1) by linarith)
      (show 0 ≤ n+2 by linarith)]



/-- The first common band exit still lies inside all but the last two representative flanks. -/
theorem terminal_flank_bound {n : ℝ} (hn : 2 < n) :
    (n-3)*((n+2)/(n-2)) < n+1 := by
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < n-2)).mpr
  nlinarith

theorem flank_survives {n z b full : ℝ} (hn : 3 ≤ n)
    (hz : 0 ≤ z) (hzmax : z ≤ (n+2)/(n-2))
    (hb : b ≤ n-3) (hfull : n+1 ≤ full) : b*z < full := by
  calc
    b*z ≤ (n-3)*z := mul_le_mul_of_nonneg_right hb hz
    _ ≤ (n-3)*((n+2)/(n-2)) :=
      mul_le_mul_of_nonneg_left hzmax (by linarith)
    _ < n+1 := terminal_flank_bound (by linarith)
    _ ≤ full := hfull

/-- At the common exit a slower band has only determinant zero or one.
The stronger `r ≤ n-2` comes from sharing the repair with a larger baseline divisor. -/
theorem exit_determinant_zero_or_one {n r m p z : ℝ} {D : ℤ}
    (hn : 2 < n) (_hr : 0 < r) (hrmax : r ≤ n-2)
    (hm : 0 < m) (hp : 0 < p) (hpP : p < m*r)
    (hz : 0 < z) (hzmax : z ≤ (n+2)/(n-2))
    (hbad : |n*m*(D : ℝ)-p*z| ≤ m*r) : D=0 ∨ D=1 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hbad
  have hnm : 0 < n*m := mul_pos (by linarith) hm
  have hmr : m*r < n*m := by nlinarith
  have hpz : 0 < p*z := mul_pos hp hz
  have hDlow : (-1 : ℝ) < D := by
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left hh hnm.le
    nlinarith
  have hzm := (le_div_iff₀ (by linarith : 0 < n-2)).mp hzmax
  have hrr : r*(z+1) ≤ 2*n := by
    have hprod := mul_le_mul_of_nonneg_right hrmax
      (show 0 ≤ z+1 by linarith)
    nlinarith
  have hpzz := mul_lt_mul_of_pos_right hpP hz
  have hmult := mul_le_mul_of_nonneg_left hrr hm.le
  have hDhigh : (D : ℝ) < 2 := by
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left hh hnm.le
    nlinarith
  have hDL : -1 < D := by exact_mod_cast hDlow
  have hDU : D < 2 := by exact_mod_cast hDhigh
  omega

theorem determinant_one_of_nonmultiple {r p b D : ℤ}
    (hD : D=0 ∨ D=1) (hcong : r ∣ D*b-p) (hnot : ¬ r ∣ p) : D=1 := by
  rcases hD with rfl | hD
  · exfalso
    apply hnot
    simpa using hcong
  · exact hD

/-- Exact scaling of a bad runner at the normalized flank clock. -/
theorem scaled_band {n r m p a j : ℤ} {z : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hbad : |(p : ℝ)*((a : ℝ)/r-z/((n : ℝ)*m*r))-j| ≤ 1/n) :
    |(n : ℝ)*m*((p*a-r*j : ℤ) : ℝ)-p*z| ≤ (m : ℝ)*r := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor : (0 : ℝ) < (n : ℝ)*m*r := by positivity
  have hid : (n : ℝ)*m*r*((p : ℝ)*((a : ℝ)/r-z/((n : ℝ)*m*r))-j) =
      (n : ℝ)*m*((p*a-r*j : ℤ) : ℝ)-p*z := by
    push_cast
    field_simp
    ring
  rw [← hid, abs_mul, abs_of_pos hfactor]
  have hmul := mul_le_mul_of_nonneg_left hbad hfactor.le
  have heq : ((n : ℝ)*m*r)*(1/n) = (m : ℝ)*r := by field_simp
  simpa only [heq] using hmul

/-- A slower nonmultiple that is bad at any permitted exit must occupy one residue class. -/
theorem slower_exit_bad_residue {n r m p a b c : ℤ} {z : ℝ}
    (hn : 2 < n) (hr : 0 < r) (hrmax : r ≤ n-2)
    (hm : 0 < m) (hp : 0 < p) (hpP : p < m*r)
    (hz : 0 < z) (hzmax : z ≤ ((n : ℝ)+2)/(n-2))
    (hunit : a*b-c*r=1) (hnot : ¬ r ∣ p)
    (hbad : ndist ((p : ℝ)*((a : ℝ)/r-z/((n : ℝ)*m*r))) ≤ 1/n) :
    r ∣ b-p := by
  let j := round ((p : ℝ)*((a : ℝ)/r-z/((n : ℝ)*m*r)))
  have hscale := scaled_band (a := a) (j := j) (by omega) hr hm hbad
  have hD := exit_determinant_zero_or_one
    (by exact_mod_cast hn) (by exact_mod_cast hr) (by exact_mod_cast hrmax)
    (by exact_mod_cast hm) (by exact_mod_cast hp) (by exact_mod_cast hpP)
    hz hzmax hscale
  have hcong : r ∣ (p*a-r*j)*b-p := by
    refine ⟨p*c-j*b, ?_⟩
    linear_combination p*hunit
  have hDone := determinant_one_of_nonmultiple hD hcong hnot
  simpa [hDone] using hcong



end LonelyRunner.SharedMiddleArithmetic

namespace LonelyRunner.ShiftedWindows















end LonelyRunner.ShiftedWindows

namespace LonelyRunner.ShiftedBlocks





















end LonelyRunner.ShiftedBlocks

namespace LonelyRunner.WholeFlankWindows

open BadCover SeparatedMulti











end LonelyRunner.WholeFlankWindows

namespace LonelyRunner.CollectivePhase

/-- A nonmultiple whose double is divisible by `r` has phase one half at
all primitive inverse centres. -/
theorem half_phase_lap {r Q : ℕ} {a b c : ℤ}
    (hr : 0 < r) (hd : r ∣ 2*Q) (hnot : ¬ r ∣ Q)
    (hu : a*b-c*(r:ℤ)=1) :
    ∃ j : ℤ, (Q:ℝ)*(a:ℝ)/r = (j:ℝ)+1/2 := by
  have hdZ : (r:ℤ) ∣ 2*(Q:ℤ) := by exact_mod_cast hd
  obtain ⟨k,hk⟩ := dvd_mul_of_dvd_left hdZ a
  have hkodd : Odd k := by
    by_contra hodd
    have heven : Even k := (Int.even_or_odd k).resolve_right hodd
    obtain ⟨l,hl⟩ := heven
    have hprod : (Q:ℤ)*a=(r:ℤ)*l := by nlinarith only [hk,hl]
    apply hnot
    have hdiv : (r:ℤ) ∣ (Q:ℤ) := by
      refine ⟨l*b-(Q:ℤ)*c, ?_⟩
      nlinarith only [congrArg (fun x : ℤ => x*(Q:ℤ)) hu,
        congrArg (fun x : ℤ => x*b) hprod]
    exact_mod_cast hdiv
  obtain ⟨j,hj⟩ := hkodd
  refine ⟨j, ?_⟩
  have hkR : 2*(Q:ℝ)*(a:ℝ)=(r:ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hjR : (k:ℝ)=2*(j:ℝ)+1 := by exact_mod_cast hj
  have hrR : (r:ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hrR).mpr
  nlinarith only [hkR,hjR]

/-- A nontrivial order-two residue requires an even modulus. -/
theorem even_modulus {r Q : ℕ} (hd : r ∣ 2*Q) (hnot : ¬ r ∣ Q) : Even r := by
  by_contra heven
  have hodd : Odd r := (Nat.even_or_odd r).resolve_left heven
  have hc : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hodd
  exact hnot (hc.dvd_mul_left.mp hd)



end LonelyRunner.CollectivePhase

namespace LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits







end LonelyRunner.CollectiveBoundaryForcing

namespace LonelyRunner.CollectiveSecondFastest

open BadCover

/-- The bad band at a half-integer phase has a nonnegative common lap index. -/
theorem half_phase_band_index {n gamma : ℝ}
    (hn : 2 < n) (hg : 1 < gamma)
    (hbad : ndist (1/2-gamma/n) ≤ 1/n) :
    ∃ j : ℤ, 0 ≤ j ∧ |gamma-n*((j:ℝ)+1/2)| ≤ 1 := by
  let j : ℤ := -round (1/2-gamma/n)
  have hn0 : 0 < n := by linarith
  have hid : gamma-n*((j:ℝ)+1/2) =
      -n*((1/2-gamma/n)-(round (1/2-gamma/n):ℤ)) := by
    dsimp [j]
    push_cast
    field_simp
    ring
  have hb : |gamma-n*((j:ℝ)+1/2)| ≤ 1 := by
    rw [hid, abs_mul, abs_neg, abs_of_pos hn0]
    have hh := mul_le_mul_of_nonneg_left hbad hn0.le
    have he : n*(1/n)=1 := by field_simp
    change n*|1/2-gamma/n-(round (1/2-gamma/n):ℤ)| ≤ 1
    simpa only [he, ndist] using hh
  refine ⟨j, ?_, hb⟩
  by_contra! hj
  have hjR : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
  have hm := mul_le_mul_of_nonneg_left (show (j:ℝ)+1/2 ≤ -1/2 by linarith) hn0.le
  linarith [(abs_le.mp hb).2]





theorem numerator_unit {r b : ℕ} (hcop : Nat.Coprime r b) :
    numerator r b*(b:ℤ)-(-Nat.gcdB b r)*(r:ℤ)=1 := by
  have hh := Nat.gcd_eq_gcd_ab b r
  rw [hcop.symm.gcd_eq_one] at hh
  dsimp [numerator]
  push_cast at hh
  nlinarith only [hh]

/-- Interior normalized flank clocks are safe for every retained baseline. -/
theorem baseline_clock_safe {n r m b v : ℕ} {a c : ℤ} {z : ℝ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hlarge : n ≤ 2*r)
    (hb : n-r ≤ b) (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hz : 0 < z) (hbz : (b:ℝ)*z < (m:ℝ)*((n:ℝ)-r))
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
    1/(n:ℝ) < ndist ((v:ℝ)*((a:ℝ)/r-z/((n:ℝ)*m*r))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast lt_trans hr hrn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbc : (n:ℝ)-r ≤ b := by rw [← Nat.cast_sub hrn.le]; exact_mod_cast hb
  have hzm : z < (m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbc hmR.le
    nlinarith
  have he : 0 < z/((n:ℝ)*m*r) := div_pos hz (by positivity)
  have hemax : z/((n:ℝ)*m*r) < 1/((n:ℝ)*r) := by
    calc
      _ < (m:ℝ)/((n:ℝ)*m*r) := div_lt_div_of_pos_right hzm (by positivity)
      _ = _ := by field_simp
  have heb : z/((n:ℝ)*m*r)*b < ((n:ℝ)-r)/((n:ℝ)*r) := by
    calc
      _ = ((b:ℝ)*z)/((n:ℝ)*m*r) := by ring
      _ < ((m:ℝ)*((n:ℝ)-r))/((n:ℝ)*m*r) :=
        div_lt_div_of_pos_right hbz (by positivity)
      _ = _ := by field_simp
  exact FailedFlank.baseline_safe_offset (n:=(n:ℤ)) (r:=(r:ℤ))
    (b:=(b:ℤ)) (a:=a) (c:=c) (v:=(v:ℤ))
    (by exact_mod_cast hr) (by exact_mod_cast hrn) (by exact_mod_cast hlarge)
    (by exact_mod_cast hbc) hu (by exact_mod_cast hv) (by exact_mod_cast hvn)
    (by exact_mod_cast hne) he hemax heb

/-- At the bounded common exit, fewer than `phi(r)-1` slower nonmultiples
cannot block every surviving primitive flank. -/
theorem exists_safe_exit {n r m : ℕ} {S : Finset ℕ} {z : ℝ}
    (hn : 5 ≤ n) (hr : 0 < r) (hrmax : r+2 ≤ n) (hm : 0 < m)
    (heven : Even r) (hcount : S.card+1 < r.totient)
    (hpos : ∀p ∈ S, 0 < p) (hslow : ∀p ∈ S, p < m*r)
    (hnot : ∀p ∈ S, ¬r ∣ p)
    (hz : 0 < z) (hzmax : z ≤ ((n:ℝ)+2)/(n-2)) :
    ∃b ∈ CollectiveUnits.primitiveFlanks n r, b ≤ n-3 ∧
      ∀p ∈ S, 1/(n:ℝ) < ndist ((p:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))) := by
  classical
  let U := (CollectiveUnits.primitiveFlanks n r).filter (fun b => b ≤ n-3)
  let B (p : ℕ) := U.filter (fun b =>
    ndist ((p:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))) ≤ 1/(n:ℝ))
  have hcap : ∀p ∈ S, (B p).card ≤ 1 := by
    intro p hp
    apply Finset.card_le_one.mpr
    intro b hb c hc
    obtain ⟨hbU,hbbad⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcU,hcbad⟩ := Finset.mem_filter.mp hc
    have hbf := (Finset.mem_filter.mp hbU).1
    have hcf := (Finset.mem_filter.mp hcU).1
    have hbunit := numerator_unit (CollectiveUnits.mem_primitiveFlanks.mp hbf).2.2
    have hcunit := numerator_unit (CollectiveUnits.mem_primitiveFlanks.mp hcf).2.2
    have hbmod := SharedMiddleArithmetic.slower_exit_bad_residue
      (n:=(n:ℤ)) (r:=(r:ℤ)) (m:=(m:ℤ)) (p:=(p:ℤ))
      (by omega) (by exact_mod_cast hr) (by omega) (by exact_mod_cast hm)
      (by exact_mod_cast hpos p hp) (by exact_mod_cast hslow p hp)
      hz hzmax hbunit (by exact_mod_cast hnot p hp) hbbad
    have hcmod := SharedMiddleArithmetic.slower_exit_bad_residue
      (n:=(n:ℤ)) (r:=(r:ℤ)) (m:=(m:ℤ)) (p:=(p:ℤ))
      (by omega) (by exact_mod_cast hr) (by omega) (by exact_mod_cast hm)
      (by exact_mod_cast hpos p hp) (by exact_mod_cast hslow p hp)
      hz hzmax hcunit (by exact_mod_cast hnot p hp) hcbad
    apply CollectiveUnits.primitiveFlanks_eq_of_dvd hbf hcf
    have heq : ((b:ℤ)-p)-((c:ℤ)-p)=(b:ℤ)-c := by ring
    simpa only [heq] using dvd_sub hbmod hcmod
  by_contra! hno
  have hcover : ∀b ∈ U, ∃p ∈ S, b ∈ B p := by
    intro b hb
    obtain ⟨hbf,hbsmall⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,hp,hbad⟩ := hno b hbf hbsmall
    exact ⟨p,hp,Finset.mem_filter.mpr ⟨hb,hbad⟩⟩
  have hh := CollectiveUnits.cover_card_le U S B 1 hcover hcap
  have hs := CollectiveUnits.terminal_survivor_card (show r ≤ n by omega) heven
  dsimp [U] at hh
  omega







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
open LonelyRunner.CollectiveSecondFastest
open BadCover

/-- Once the canonical cover has forced the half-phase resonance, its common
band exit supplies a strict time. This is the geometric half of the theorem. -/
theorem solution {n r m Q : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hr : 0 < r) (hrmax : r+2 ≤ n) (hm : 2 ≤ m)
    (hrR : r ∈ R) (hlarge : n ≤ 2*r)
    (hfull : n < m*(n-r)) (hpq : m*r < Q)
    (hWpos : ∀p ∈ W, 0 < p)
    (hslow : ∀p ∈ (W.erase (m*r)).erase Q, p < m*r)
    (hunique : ∀p ∈ W.erase (m*r), ¬r ∣ p)
    (hQ : Q ∈ W) (hcount : ((W.erase (m*r)).erase Q).card+1 < r.totient)
    (hd : r ∣ 2*Q)
    (hband : ndist (1/2-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ)) ≤ 1/(n:ℝ)) :
    SeparatedMulti.HasStrictTime n R W := by
  classical
  have hrn : r < n := by omega
  have hm0 : 0 < m := by omega
  have hnR : (0:ℝ) < n := by positivity
  have hrR' : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  have hn5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hQne : Q ≠ m*r := by omega
  have hnotQ : ¬r ∣ Q := hunique Q (Finset.mem_erase.mpr ⟨hQne,hQ⟩)
  have heven := CollectivePhase.even_modulus hd hnotQ
  let gamma : ℝ := (Q:ℝ)/((m:ℝ)*r)
  have hg1 : 1 < gamma := by
    apply (lt_div_iff₀ (mul_pos hmR hrR')).mpr
    simpa using (show (m:ℝ)*r < Q by exact_mod_cast hpq)
  obtain ⟨j,hj,hjband⟩ := half_phase_band_index (by linarith : (2:ℝ) < n) hg1 hband
  let T : ℝ := (n:ℝ)*((j:ℝ)+1/2)
  let z₀ : ℝ := (T+1)/gamma
  have hjR : (0:ℝ) ≤ j := by exact_mod_cast hj
  have hT : (n:ℝ)/2 ≤ T := by dsimp [T]; nlinarith
  have hz := SharedMiddleArithmetic.half_phase_exit_bound
    (n:=(n:ℝ)) (T:=T) (gamma:=gamma) (by linarith) hT (by linarith) hjband
  have hz0 : 0 < z₀ := by dsimp [z₀]; linarith [hz.1]
  have hzmax : z₀ ≤ ((n:ℝ)+2)/(n-2) := hz.2
  let L := (W.erase (m*r)).erase Q
  obtain ⟨b,hbf,hbsmall,hbsafe⟩ := exists_safe_exit hn hr hrmax hm0 heven hcount
    (fun p hp => hWpos p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)))
    hslow (fun p hp => hunique p (Finset.mem_of_mem_erase hp)) hz0 hzmax
  obtain ⟨hb,hbn,hbcop⟩ := CollectiveUnits.mem_primitiveFlanks.mp hbf
  let a := numerator r b
  let c := -Nat.gcdB b r
  have hu : a*(b:ℤ)-c*(r:ℤ)=1 := numerator_unit hbcop
  obtain ⟨J,hJ⟩ := CollectivePhase.half_phase_lap hr hd hnotQ hu
  let clock : ℝ → ℝ := fun z => (a:ℝ)/r-z/((n:ℝ)*m*r)
  have hclock : Continuous clock := by fun_prop
  have hPclock : ∀z, ((m*r:ℕ):ℝ)*clock z=((m:ℤ)*a:ℤ)-z/(n:ℝ) := by
    intro z
    dsimp [clock]
    push_cast
    field_simp
  have hQclock : ∀z, (Q:ℝ)*clock z=(J:ℝ)+1/2-gamma*z/(n:ℝ) := by
    intro z
    dsimp [clock,gamma]
    rw [mul_sub, ← hJ]
    field_simp
  have hbz : (b:ℝ)*z₀ < (m:ℝ)*((n:ℝ)-r) := by
    apply SharedMiddleArithmetic.flank_survives (by linarith : (3:ℝ) ≤ n)
      hz0.le hzmax
    · have : (b:ℝ) ≤ (n-3:ℕ) := by exact_mod_cast hbsmall
      rw [Nat.cast_sub (by omega : 3 ≤ n)] at this
      exact this
    · have hh : (n:ℝ)+1 ≤ (m:ℝ)*(n-r:ℕ) := by
        exact_mod_cast (show n+1 ≤ m*(n-r) by omega)
      rw [Nat.cast_sub hrn.le] at hh
      exact hh
  let S := ((Finset.range n).filter (fun v => 0 < v ∧ v ∉ R)) ∪ L
  have hS : ∀v ∈ S, 1/(n:ℝ) < ndist ((v:ℝ)*clock z₀) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hvn,hv0,hvR⟩ := Finset.mem_filter.mp hv
      exact baseline_clock_safe hr hrn hm0 hlarge hb hu hz0 hbz hv0
        (Finset.mem_range.mp hvn) (by rintro rfl; exact hvR hrR)
    · exact hbsafe v hv
  have hZ : ((n:ℝ)+2)/(n-2) < (n:ℝ)-1 := by
    apply (div_lt_iff₀ (by linarith : (0:ℝ) < n-2)).mpr
    nlinarith
  have he : gamma*z₀=T+1 := by dsimp [z₀]; field_simp
  obtain ⟨z,hzz,hPz,hQz,hSz⟩ := clock_exit_escape S clock hclock
    (by linarith : (2:ℝ) < n) (by linarith : 0 < gamma) hz.1
    (hzmax.trans_lt hZ) he (show T=(n:ℝ)*((j:ℝ)+1/2) from rfl)
    hPclock hQclock hS
  refine ⟨clock z,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hvW
  · exact hSz v (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hvn,hv,hvR⟩))
  · by_cases hvP : v=m*r
    · simpa [hvP] using hPz
    · by_cases hvQ : v=Q
      · simpa [hvQ] using hQz
      · exact hSz v (Finset.mem_union_right _
          (Finset.mem_erase.mpr ⟨hvQ,Finset.mem_erase.mpr ⟨hvP,hvW⟩⟩))
