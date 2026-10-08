-- Prove2me | solution 1 for LonelyRunner.SharedFastest.strict_of_shared_fastest
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:11:45.754208+00:00
-- url     : https://prove2.me/submissions/3e8c4df8-0600-47d7-b2a0-81a361e61cbc

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_FastestBoundary_boundary_blocker

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.Farey

theorem exists_determinant_one {r s : ℤ} (h : Int.gcd r s = 1) :
    ∃ a b : ℤ, b * r - a * s = 1 := by
  refine ⟨-Int.gcdB r s, Int.gcdA r s, ?_⟩
  have hb := Int.gcd_eq_gcd_ab r s
  rw [h] at hb
  norm_num at hb
  linear_combination -hb

















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





/-- A slower speed can meet this boundary only with determinant zero or one. -/
theorem determinant_zero_or_one {n r m q D : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hq : 0 < q)
    (hqp : q < m*r) (hnear : |n*m*D-q| ≤ m*r) : D=0 ∨ D=1 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hnear
  have hnm : 0 < n*m := mul_pos (lt_trans hr hrn) hm
  have hmr : m*r < n*m := by nlinarith only [mul_lt_mul_of_pos_left hrn hm]
  have hD0 : 0 ≤ D := by
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left (show D ≤ -1 by omega) hnm.le
    nlinarith only [hmul,hlo,hmr,hq]
  have hD1 : D ≤ 1 := by
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ D by omega) hnm.le
    nlinarith only [hmul,hhi,hmr,hqp]
  omega



/-- For a slower nonmultiple, blocking a failed boundary forces one residue
class and a lower bound on its speed. -/
theorem slower_bad_residue {n r m q b : ℕ} {a c : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hq : 0 < q)
    (hqp : q < m*r) (hnot : ¬ r ∣ q)
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hbad : ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) ≤ 1/n) :
    m*(n-r) ≤ q ∧ q % r = b % r := by
  let j := round ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)))
  have hnear := NearData.scale (n := (n:ℤ)) (r := (r:ℤ)) (m := (m:ℤ))
    (q := (q:ℤ)) (a := a) (j := j)
    (by exact_mod_cast lt_trans hr hrn) (by exact_mod_cast hr)
    (by exact_mod_cast hm) hbad
  have hD := determinant_zero_or_one (by exact_mod_cast hr) (by exact_mod_cast hrn)
    (by exact_mod_cast hm) (by exact_mod_cast hq) (by exact_mod_cast hqp) hnear
  have hD1 : (q:ℤ)*a-(r:ℤ)*j=1 := by
    rcases hD with hD0 | hD1
    · exfalso
      apply hnot
      have hd : (r:ℤ) ∣ (q:ℤ) := by
        refine ⟨(b:ℤ)*j-c*q,?_⟩
        nlinarith [congrArg (fun x : ℤ => x*q) hu,
          congrArg (fun x : ℤ => x*(b:ℤ)) hD0]
      exact_mod_cast hd
    · exact hD1
  constructor
  · have hi := (abs_le.mp hnear).2
    rw [hD1] at hi
    have hb : (m:ℤ)*((n:ℤ)-r) ≤ q := by nlinarith only [hi]
    rw [← Nat.cast_sub hrn.le] at hb
    exact_mod_cast hb
  · apply Nat.ModEq.symm
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(b:ℤ)*j-c*q,?_⟩
    nlinarith [congrArg (fun x : ℤ => x*q) hu,
      congrArg (fun x : ℤ => x*(b:ℤ)) hD1]







/-- Every failed unit residue needs a slower insertion in that same residue
class, if the fastest insertion is the only multiple of this deletion. -/
theorem failed_unit_covered {n r m b : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W)
    (hab : n-r ≤ b) (hfail : b < m*(n-r)) (hcop : Nat.Coprime r b) :
    ∃ q ∈ W.erase (m*r), m*(n-r) ≤ q ∧ q % r = b % r := by
  have hr : 0 < r := by omega
  obtain ⟨a',c',hu'⟩ := Farey.exists_determinant_one
    (r := (r:ℤ)) (s := (b:ℤ)) (by simpa using hcop.gcd_eq_one)
  let a := -a'
  let c := -c'
  have hu : a*(b:ℤ)-c*(r:ℤ)=1 := by dsimp [a,c]; nlinarith only [hu']
  obtain ⟨q,hq,hbad⟩ := boundary_blocker hn hrR hlarge hrn hm hab hfail hu hno
  exact ⟨q,hq,slower_bad_residue hr hrn (by omega)
    (hW q (Finset.mem_of_mem_erase hq)) (hmax q hq) (hunique q hq) hu hbad⟩





theorem residue_cover {n r m : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    failedResidues n r m ⊆ (eligible n r m W).image (· % r) := by
  intro x hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hb,hcop⟩ := Finset.mem_filter.mp hb
  obtain ⟨hab,hfail⟩ := Finset.mem_Ico.mp hb
  obtain ⟨q,hq,hbound,heq⟩ := failed_unit_covered hn hrR hlarge hrn hm hW
    hmax hunique hno hab hfail hcop
  exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hbound⟩,heq⟩

theorem residue_count_bound {n r m : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    (failedResidues n r m).card ≤ (eligible n r m W).card :=
  (Finset.card_le_card (residue_cover hn hrR hlarge hrn hm hW hmax hunique hno)).trans
    (Finset.card_image_le)

/-- In particular, three inserted speeds cannot repair three distinct failed
unit residues of a uniquely matched fastest insertion. -/
theorem strict_of_three_residues {n r m : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hpW : m*r ∈ W) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hcard : W.card ≤ 3) (hunits : 3 ≤ (failedResidues n r m).card) :
    SeparatedMulti.HasStrictTime n R W := by
  by_contra hno
  have hb := residue_count_bound hn hrR hlarge hrn hm hW hmax hunique hno
  have he : (eligible n r m W).card ≤ (W.erase (m*r)).card :=
    Finset.card_filter_le _ _
  have hc := Finset.card_erase_of_mem hpW
  omega

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

/-- Every modulus r>=7 has a unit other than +1 and -1.
The proof explicitly constructs one, including both even residue classes. -/
theorem exists_middle_unit {r : ℕ} (hr : 7 ≤ r) :
    ∃ u : ℕ, 1 < u ∧ u < r-1 ∧ Nat.Coprime r u := by
  by_cases hodd : r % 2 = 1
  · exact ⟨2,by omega,by omega,Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)⟩
  · let k := r/2
    have hrk : r=2*k := by dsimp [k]; omega
    have hk : 4 ≤ k := by omega
    by_cases hkeven : k % 2 = 0
    · let u := k-1
      have huodd : Odd u := Nat.odd_iff.mpr (by dsimp [u]; omega)
      have hu2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr huodd
      have heq : r=2*u+2 := by dsimp [u]; omega
      have hcop : Nat.Coprime u r := by
        rw [heq,Nat.coprime_mul_right_add_right]
        exact hu2
      exact ⟨u,by dsimp [u]; omega,by dsimp [u]; omega,hcop.symm⟩
    · let u := k-2
      have huodd : Odd u := Nat.odd_iff.mpr (by dsimp [u]; omega)
      have hu2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr huodd
      have hu4 : Nat.Coprime u 4 := by simpa using hu2.mul_right hu2
      have heq : r=2*u+4 := by dsimp [u]; omega
      have hcop : Nat.Coprime u r := by
        rw [heq,Nat.coprime_mul_right_add_right]
        exact hu4
      exact ⟨u,by dsimp [u]; omega,by dsimp [u]; omega,hcop.symm⟩

/-- Full failed windows include every unit residue of their modulus. -/
theorem unit_mem_failedResidues {n r m u : ℕ}
    (hlarge : n ≤ 2*r) (hrn : r < n) (hfull : n ≤ m*(n-r))
    (hu : u < r) (hcop : Nat.Coprime r u) : u ∈ failedResidues n r m := by
  have hc : n-r ≤ r := by omega
  have hnr : n-r+r=n := Nat.sub_add_cancel hrn.le
  by_cases huc : n-r ≤ u
  · apply Finset.mem_image.mpr
    exact ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨huc,by omega⟩,hcop⟩,
      Nat.mod_eq_of_lt hu⟩
  · apply Finset.mem_image.mpr
    refine ⟨u+r,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,
      Nat.coprime_add_self_right.mpr hcop⟩,?_⟩
    simpa using Nat.mod_eq_of_lt hu

theorem three_residues_of_full_window {n r m : ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hfull : n ≤ m*(n-r)) : 3 ≤ (failedResidues n r m).card := by
  obtain ⟨u,hu1,hur,hcop⟩ := exists_middle_unit hr
  have h1 : 1 ∈ failedResidues n r m :=
    unit_mem_failedResidues hlarge hrn hfull (by omega) (Nat.coprime_one_right r)
  have hu : u ∈ failedResidues n r m :=
    unit_mem_failedResidues hlarge hrn hfull (by omega) hcop
  have hm : r-1 ∈ failedResidues n r m := by
    apply unit_mem_failedResidues hlarge hrn hfull (by omega)
    exact (Nat.coprime_self_sub_right (by omega : 1 ≤ r)).mpr (Nat.coprime_one_right r)
  have hsub : ({1,u,r-1} : Finset ℕ) ⊆ failedResidues n r m := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({1,u,r-1} : Finset ℕ).card=3 := by
    simp [show 1 ≠ u by omega,show 1 ≠ r-1 by omega,show u ≠ r-1 by omega]
  rw [← hcard]
  exact Finset.card_le_card hsub







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
open LonelyRunner.SharedFastest
open FastestBoundary

/-- If the fastest insertion is shared by r<s and uniquely supplies r>=7,
at most three insertions cannot prevent a strictly lonely time. -/
theorem solution {n r s m k : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hr : 7 ≤ r) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hm : 2 ≤ m) (hk : 0 < k) (heq : m*r=k*s)
    (hpW : m*r ∈ W) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hcard : W.card ≤ 3) : SeparatedMulti.HasStrictTime n R W := by
  apply strict_of_three_residues hn hrR hlarge (lt_trans hrs hsn) hm hpW hW hmax hunique hcard
  exact three_residues_of_full_window hr hlarge (lt_trans hrs hsn)
    (shared_multiple_full_window (by omega) hrs hsn hk heq).le
