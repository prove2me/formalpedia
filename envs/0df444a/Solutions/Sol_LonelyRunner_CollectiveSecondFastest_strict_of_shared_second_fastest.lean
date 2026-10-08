-- Prove2me | solution 1 for LonelyRunner.CollectiveSecondFastest.strict_of_shared_second_fastest
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:16:41.320653+00:00
-- url     : https://prove2.me/submissions/e5d992f8-2b40-4ff8-a4e2-6f4208257a35

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_CollectiveBoundaryForcing_second_fastest_forces_parity
import Theorems.Thm_LonelyRunner_CollectiveSecondFastest_strict_of_half_phase_band

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m

@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

































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



theorem scale {n r m q a j : ℤ} (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hnear : |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n) :
    |n*m*(q*a-r*j)-q| ≤ m*r := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heq : (n:ℝ)*m*r*((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j) =
      (n:ℝ)*m*((q:ℝ)*a-r*j)-q := by field_simp; ring
  have hh : |(n:ℝ)*m*((q:ℝ)*a-r*j)-q| ≤ (m:ℝ)*r := by
    calc
      _ = ((n:ℝ)*m*r)*|(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| := by
        rw [← heq,abs_mul,abs_of_pos (mul_pos (mul_pos hnR hmR) hrR)]
      _ ≤ ((n:ℝ)*m*r)*(1/n) :=
        mul_le_mul_of_nonneg_left hnear (mul_pos (mul_pos hnR hmR) hrR).le
      _ = _ := by field_simp
  exact_mod_cast hh



end LonelyRunner.NearData

namespace LonelyRunner.FastestBoundary

/-- The scaled band inequality also implies the real boundary inequality. -/
theorem near_of_scale {n r m q a j : ℤ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hscaled : |n*m*(q*a-r*j)-q| ≤ m*r) :
    |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heq : (n:ℝ)*m*r*((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j) =
      (n:ℝ)*m*((q:ℝ)*a-r*j)-q := by field_simp; ring
  have hh : |(n:ℝ)*m*((q:ℝ)*a-r*j)-q| ≤ (m:ℝ)*r := by exact_mod_cast hscaled
  rw [← heq,abs_mul,abs_of_pos (mul_pos (mul_pos hnR hmR) hrR)] at hh
  have hv : ((n:ℝ)*m*r)*(1/n)=(m:ℝ)*r := by field_simp
  rw [← hv] at hh
  exact (mul_le_mul_iff_right₀ (mul_pos (mul_pos hnR hmR) hrR)).mp hh

/-- An exact integer test for an arbitrary insertion at a failed boundary.
The possible D lie in an interval of length 2*r/n, less than two for r<n. -/
theorem bad_iff_determinant {n r m q b a c : ℤ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) (hu : a*b-c*r=1) :
    ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) ≤ 1/n ↔
      ∃ D : ℤ, |n*m*D-q| ≤ m*r ∧ r ∣ D*b-q := by
  constructor
  · intro hbad
    let j := round ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)))
    refine ⟨q*a-r*j,NearData.scale hn hr hm hbad,?_⟩
    refine ⟨q*c-j*b,?_⟩
    nlinarith [congrArg (fun x : ℤ => x*q) hu]
  · rintro ⟨D,hD,k,hk⟩
    let j := D*c-k*a
    have heq : q*a-r*j=D := by
      dsimp [j]
      nlinarith [congrArg (fun x : ℤ => x*D) hu,
        congrArg (fun x : ℤ => x*a) hk]
    have hh : |n*m*(q*a-r*j)-q| ≤ m*r := by rw [heq]; exact hD
    exact (ndist_le_abs_sub _ j).trans (near_of_scale hn hr hm hh)

























end LonelyRunner.FastestBoundary

namespace LonelyRunner.CollectiveBoundary























end LonelyRunner.CollectiveBoundary

namespace LonelyRunner.SharedFastest

open FastestBoundary

/-- A common multiple of r<s<n makes the smaller deletion's failed window
contain an entire residue period. -/
theorem shared_multiple_full_window {n r s m k : ℕ}
    (_hr : 0 < r) (hrs : r < s) (hsn : s < n) (hk : 0 < k)
    (heq : m*r=k*s) : n < m*(n-r) := by
  have hkm : k < m := by
    by_contra! hh
    have hle := Nat.mul_le_mul_right r hh
    have hlt := Nat.mul_lt_mul_of_pos_left hrs hk
    omega
  have hrsub : r+(s-r)=s := Nat.add_sub_of_le hrs.le
  have hnrsub : r+(n-r)=n := Nat.add_sub_of_le (lt_trans hrs hsn).le
  have hmul := Nat.mul_le_mul_right r (show k+1 ≤ m by omega)
  have hlow : r ≤ k*(s-r) := by nlinarith only [hrsub,hmul,heq]
  have hhigh : k*(s-r) < (m-1)*(n-r) := by
    calc
      _ < k*(n-r) := Nat.mul_lt_mul_of_pos_left (by omega) hk
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hm : 1 ≤ m := by omega
  have hsplit : m*(n-r)=(m-1)*(n-r)+(n-r) := by
    nlinarith only [Nat.sub_add_cancel hm]
  omega













end LonelyRunner.SharedFastest

namespace LonelyRunner.CollectiveUnits





















@[simp] theorem mem_primitiveFlanks {n r b : ℕ} :
    b ∈ primitiveFlanks n r ↔ n-r ≤ b ∧ b < n ∧ Nat.Coprime r b := by
  simp [primitiveFlanks, and_assoc]

















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

/-- Reuse the established shared-divisor implication for the full failed period. -/
theorem shared_full_period {n r s m k : ℕ}
    (hr : 0 < r) (hrs : r < s) (hsn : s < n) (hk : 0 < k)
    (heq : m * r = k * s) : n < m * (n-r) :=
  SharedFastest.shared_multiple_full_window hr hrs hsn hk heq



















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





end LonelyRunner.CollectivePhase

namespace LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits







end LonelyRunner.CollectiveBoundaryForcing

namespace LonelyRunner.CollectiveSecondFastest

open BadCover







theorem numerator_unit {r b : ℕ} (hcop : Nat.Coprime r b) :
    numerator r b*(b:ℤ)-(-Nat.gcdB b r)*(r:ℤ)=1 := by
  have hh := Nat.gcd_eq_gcd_ab b r
  rw [hcop.symm.gcd_eq_one] at hh
  dsimp [numerator]
  push_cast at hh
  nlinarith only [hh]







/-- An active fast determinant at one primitive boundary identifies the same
half-phase bad band at every primitive centre. -/
theorem half_phase_band_of_block {n r m Q b : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hd : r ∣ 2*Q) (hnot : ¬r ∣ Q) (hcop : Nat.Coprime r b)
    (hblock : CollectiveBoundary.Blocks (n:ℤ) r m Q b) :
    ndist (1/2-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ)) ≤ 1/(n:ℝ) := by
  have hu := numerator_unit hcop
  obtain ⟨J,hJ⟩ := CollectivePhase.half_phase_lap hr hd hnot hu
  have hbad := (FastestBoundary.bad_iff_determinant
    (n:=(n:ℤ)) (r:=(r:ℤ)) (m:=(m:ℤ)) (q:=(Q:ℤ))
    (by exact_mod_cast hn) (by exact_mod_cast hr) (by exact_mod_cast hm) hu).mpr hblock
  have heq : (Q:ℝ)*((numerator r b:ℝ)/r-1/((n:ℝ)*m*r)) =
      (1/2-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ))+(J:ℝ) := by
    calc
      _ = (Q:ℝ)*(numerator r b:ℝ)/r-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ) := by
        field_simp
      _ = _ := by rw [hJ]; ring
  push_cast at hbad
  rw [heq, ndist_add_int] at hbad
  exact hbad



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

/-- A unique repair shared with a larger baseline divisor cannot be the
second-fastest insertion when the primitive-unit capacity is large enough.
The conclusion is an actual strict time, with arbitrary additional deletions. -/
theorem solution {n r s m k Q ell : ℕ} {R W : Finset ℕ}
    (hell : 3 ≤ ell) (hcard : W.card ≤ ell)
    (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 2 ≤ m) (hk : 0 < k) (hshared : m*r=k*s)
    (hP : m*r ∈ W) (hQ : Q ∈ W) (hpq : m*r < Q)
    (hWpos : ∀p ∈ W, 0 < p)
    (hslow : ∀p ∈ (W.erase (m*r)).erase Q, p < m*r)
    (hunique : ∀p ∈ W.erase (m*r), ¬r ∣ p)
    (hphi : 2*ell-2 ≤ r.totient) :
    SeparatedMulti.HasStrictTime n R W := by
  classical
  have hphile := Nat.totient_le r
  have hr : 0 < r := by omega
  have hn : 5 ≤ n := by omega
  have hrmax : r+2 ≤ n := by omega
  have hrn : r < n := by omega
  have hfull := SharedMiddleArithmetic.shared_full_period hr hrs hsn hk hshared
  have hQT : Q ∈ W.erase (m*r) := Finset.mem_erase.mpr ⟨by omega,hQ⟩
  have hLc : ((W.erase (m*r)).erase Q).card+2=W.card := by
    have ht := Finset.card_erase_add_one hP
    have hl := Finset.card_erase_add_one hQT
    omega
  have hcount : ((W.erase (m*r)).erase Q).card+1 < r.totient := by omega
  by_contra hno
  obtain ⟨hd,b,hbf,hblock⟩ := CollectiveBoundaryForcing.second_fastest_forces_parity
    hn hrR hlarge hrn hm hfull.le hP hQ hpq hWpos hslow hunique
    hell hcard hphi hno
  have hband := half_phase_band_of_block (by omega : 0 < n) hr (by omega : 0 < m)
    hd (hunique Q hQT) (CollectiveUnits.mem_primitiveFlanks.mp hbf).2.2 hblock
  exact hno (strict_of_half_phase_band hn hr hrmax hm hrR hlarge hfull hpq
    hWpos hslow hunique hQ hcount hd hband)
