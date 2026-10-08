-- Prove2me | solution 1 for LonelyRunner.CollectiveBoundaryForcing.second_fastest_forces_parity
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:11:42.066982+00:00
-- url     : https://prove2.me/submissions/9634aa93-a800-4fe5-be3d-4680cfae8f84

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_FastestBoundary_boundary_blocker

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m



































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







/-- A general finite arithmetic obstruction, allowing faster insertions,
overlapping bands, and shared multiples of deleted speeds. -/
theorem failed_unit_has_determinant {n r m b : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hcop : Nat.Coprime r b) (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    ∃ q ∈ W.erase (m*r), ∃ D : ℤ,
      |(n:ℤ)*m*D-q| ≤ (m:ℤ)*r ∧ (r:ℤ) ∣ D*b-q := by
  have hr : 0 < r := by omega
  obtain ⟨a',c',hu'⟩ := Farey.exists_determinant_one
    (r := (r:ℤ)) (s := (b:ℤ)) (by simpa using hcop.gcd_eq_one)
  let a := -a'
  let c := -c'
  have hu : a*(b:ℤ)-c*(r:ℤ)=1 := by dsimp [a,c]; nlinarith only [hu']
  obtain ⟨q,hq,hbad⟩ := boundary_blocker hn hrR hlarge hrn hm hab hfail hu hno
  exact ⟨q,hq,(bad_iff_determinant (by omega) (by exact_mod_cast hr)
    (by omega) hu).mp hbad⟩















end LonelyRunner.FastestBoundary

namespace LonelyRunner.CollectiveBoundary





theorem candidate_close {n r m q D E : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m)
    (hD : Candidate n r m q D) (hE : Candidate n r m q E) :
    |D-E| ≤ 1 := by
  obtain ⟨hDl,hDu⟩ := abs_le.mp hD
  obtain ⟨hEl,hEu⟩ := abs_le.mp hE
  have hnm : 0 < n*m := mul_pos (lt_trans hr hrn) hm
  have hmr : m*r < n*m := by nlinarith [mul_lt_mul_of_pos_left hrn hm]
  apply abs_le.mpr
  constructor
  · by_contra h
    have hgap : 2 ≤ E-D := by omega
    have hmul := mul_le_mul_of_nonneg_left hgap hnm.le
    nlinarith only [hEu,hDl,hmul,hmr]
  · by_contra h
    have hgap : 2 ≤ D-E := by omega
    have hmul := mul_le_mul_of_nonneg_left hgap hnm.le
    nlinarith only [hDu,hEl,hmul,hmr]

/-- A unit boundary label writes its determinant in the ideal generated by r,q. -/
theorem determinant_in_ideal {r q D b : ℤ}
    (hb : IsCoprime r b) (hd : r ∣ D*b-q) :
    ∃ x y : ℤ, x*r+y*q=D := by
  obtain ⟨u,v,hu⟩ := hb
  obtain ⟨k,hk⟩ := hd
  refine ⟨D*u+v*k,v,?_⟩
  linear_combination D*hu-v*hk

theorem determinant_coprime {r q D b : ℤ}
    (hq : IsCoprime r q) (hd : r ∣ D*b-q) : IsCoprime r D := by
  obtain ⟨x,y,hxy⟩ := hq
  obtain ⟨k,hk⟩ := hd
  refine ⟨x-y*k,y*b,?_⟩
  linear_combination hxy+y*hk

theorem same_det_residue_of_coprime {r q D b c : ℤ}
    (hq : IsCoprime r q) (hb : r ∣ D*b-q) (hc : r ∣ D*c-q) :
    r ∣ b-c := by
  have hD := determinant_coprime hq hb
  apply hD.dvd_of_dvd_mul_left
  convert dvd_sub hb hc using 1; ring

/-- Noncoprime insertions have just one determinant on all unit boundaries. -/
theorem same_det_of_not_coprime {n r m q D E b c : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m)
    (hq : ¬ IsCoprime r q) (hb : IsCoprime r b) (hc : IsCoprime r c)
    (hD : Candidate n r m q D) (hE : Candidate n r m q E)
    (hd : r ∣ D*b-q) (he : r ∣ E*c-q) : D=E := by
  have hclose := abs_le.mp (candidate_close hr hrn hm hD hE)
  obtain ⟨x,y,hxy⟩ := determinant_in_ideal hb hd
  obtain ⟨u,v,huv⟩ := determinant_in_ideal hc he
  by_contra hne
  apply hq
  have hcases : D-E=1 ∨ E-D=1 := by omega
  rcases hcases with hplus | hminus
  · refine ⟨x-u,y-v,?_⟩
    linear_combination hxy-huv+hplus
  · refine ⟨u-x,v-y,?_⟩
    linear_combination huv-hxy+hminus

/-- The coprime blocker covers at most two distinct unit residues.
The labels may live in any finite type with an injective residue map. -/
theorem coprime_blocker_card {α : Type*} [DecidableEq α]
    {n r m q : ℤ} (S : Finset α) (f : α → ℤ)
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hq : IsCoprime r q)
    (hinj : ∀ b ∈ S, ∀ c ∈ S, r ∣ f b-f c → b=c)
    (hblock : ∀ b ∈ S, Blocks n r m q (f b)) : S.card ≤ 2 := by
  by_contra hcard
  obtain ⟨b,c,d,hb,hc,hd,hbc,hbd,hcd⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < S.card by omega)
  obtain ⟨D,hD,hDb⟩ := hblock b hb
  obtain ⟨E,hE,hEc⟩ := hblock c hc
  obtain ⟨F,hF,hFd⟩ := hblock d hd
  have hDE : D ≠ E := by
    intro heq
    apply hbc
    apply hinj b hb c hc
    rw [← heq] at hEc
    exact same_det_residue_of_coprime hq hDb hEc
  have hDF : D ≠ F := by
    intro heq
    apply hbd
    apply hinj b hb d hd
    rw [← heq] at hFd
    exact same_det_residue_of_coprime hq hDb hFd
  have hEF : E ≠ F := by
    intro heq
    apply hcd
    apply hinj c hc d hd
    rw [← heq] at hFd
    exact same_det_residue_of_coprime hq hEc hFd
  have hDEc := abs_le.mp (candidate_close hr hrn hm hD hE)
  have hDFc := abs_le.mp (candidate_close hr hrn hm hD hF)
  have hEFc := abs_le.mp (candidate_close hr hrn hm hE hF)
  omega

theorem slower_block_residue {n r m q b : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hq : 0 < q)
    (hqp : q < m*r) (hnot : ¬ r ∣ q) (hb : Blocks n r m q b) :
    r ∣ b-q := by
  obtain ⟨D,hD,hd⟩ := hb
  rcases FastestBoundary.determinant_zero_or_one hr hrn hm hq hqp hD with h0 | h1
  · subst D
    exact False.elim (hnot (by simpa using hd))
  · subst D
    simpa using hd

theorem slower_blocker_card {α : Type*} [DecidableEq α]
    {n r m q : ℤ} (S : Finset α) (f : α → ℤ)
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hq : 0 < q)
    (hqp : q < m*r) (hnot : ¬ r ∣ q)
    (hinj : ∀ b ∈ S, ∀ c ∈ S, r ∣ f b-f c → b=c)
    (hblock : ∀ b ∈ S, Blocks n r m q (f b)) : S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb c hc
  apply hinj b hb c hc
  have hbd := slower_block_residue hr hrn hm hq hqp hnot (hblock b hb)
  have hcd := slower_block_residue hr hrn hm hq hqp hnot (hblock c hc)
  have heq : (f b-q)-(f c-q)=f b-f c := by ring
  simpa only [heq] using dvd_sub hbd hcd

/-- A noncoprime blocker covering opposite unit labels forces the parity resonance. -/
theorem opposite_blocks_dvd_twice {n r m q b c : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m)
    (hq : ¬ IsCoprime r q) (hb : IsCoprime r b) (hc : IsCoprime r c)
    (hopp : r ∣ b+c)
    (hbb : Blocks n r m q b) (hbc : Blocks n r m q c) : r ∣ 2*q := by
  obtain ⟨D,hD,hd⟩ := hbb
  obtain ⟨E,hE,he⟩ := hbc
  have hDE := same_det_of_not_coprime hr hrn hm hq hb hc hD hE hd he
  subst E
  have hsum : r ∣ D*(b+c)-2*q := by
    have heq : (D*b-q)+(D*c-q)=D*(b+c)-2*q := by ring
    simpa only [heq] using dvd_add hd he
  have hmul : r ∣ D*(b+c) := dvd_mul_of_dvd_right hopp D
  have heq : D*(b+c)-(D*(b+c)-2*q)=2*q := by ring
  simpa only [heq] using dvd_sub hmul hsum

end LonelyRunner.CollectiveBoundary

namespace LonelyRunner.SharedFastest

open FastestBoundary















end LonelyRunner.SharedFastest

namespace LonelyRunner.CollectiveUnits



@[simp] theorem mem_units {r u : ℕ} : u ∈ units r ↔ u < r ∧ Nat.Coprime r u := by
  simp [units]

@[simp] theorem card_units (r : ℕ) : (units r).card = r.totient := rfl

theorem unit_pos {r u : ℕ} (hr : 1 < r) (hu : u ∈ units r) : 0 < u := by
  obtain ⟨_, hc⟩ := mem_units.mp hu
  by_contra! hh
  have : u = 0 := by omega
  subst u
  simp only [Nat.coprime_zero_right] at hc
  omega

theorem opposite_mem_units {r u : ℕ} (hr : 1 < r) (hu : u ∈ units r) :
    r-u ∈ units r := by
  obtain ⟨hur, hc⟩ := mem_units.mp hu
  have hup := unit_pos hr hu
  exact mem_units.mpr ⟨by omega,
    (Nat.coprime_self_sub_right hur.le).mpr hc⟩





/-- A set of units containing no opposite pair occupies at most half the units. -/
theorem no_opposite_half_card {r : ℕ} {B : Finset ℕ}
    (hr : 1 < r) (hB : B ⊆ units r)
    (hopp : ∀ u ∈ B, r-u ∉ B) : 2*B.card ≤ r.totient := by
  let C := B.image (fun u => r-u)
  have hC : C ⊆ units r := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact opposite_mem_units hr (hB hu)
  have hc : C.card = B.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv heq
    dsimp at heq
    have hur := (mem_units.mp (hB hu)).1
    have hvr := (mem_units.mp (hB hv)).1
    omega
  have hdis : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro u hu huc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp huc
    exact hopp v hv hu
  have hsub : B ∪ C ⊆ units r := Finset.union_subset hB hC
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hc, card_units] at hh
  omega

/-- Every unit lifts to the single period of primitive flank representatives. -/
theorem lift_unit {n r u : ℕ} (hlarge : n ≤ 2*r) (hrn : r < n)
    (hu : u ∈ units r) :
    ∃ b : ℕ, n-r ≤ b ∧ b < n ∧ Nat.Coprime r b ∧ b%r=u := by
  obtain ⟨hur, hc⟩ := mem_units.mp hu
  by_cases hb : n-r ≤ u
  · exact ⟨u, hb, by omega, hc, Nat.mod_eq_of_lt hur⟩
  · refine ⟨u+r, by omega, by omega, Nat.coprime_add_self_right.mpr hc, ?_⟩
    simpa using Nat.mod_eq_of_lt hur



@[simp] theorem mem_primitiveFlanks {n r b : ℕ} :
    b ∈ primitiveFlanks n r ↔ n-r ≤ b ∧ b < n ∧ Nat.Coprime r b := by
  simp [primitiveFlanks, and_assoc]











/-- A set larger than half of the unit group contains an opposite pair. -/
theorem exists_opposite_pair {r : ℕ} {B : Finset ℕ}
    (hr : 1 < r) (hB : B ⊆ units r) (hcard : r.totient < 2*B.card) :
    ∃ u ∈ B, r-u ∈ B := by
  by_contra! hh
  have := no_opposite_half_card hr hB hh
  omega





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

private theorem blocks_of_dvd_sub {n r m q b c : ℤ}
    (hbc : r ∣ b-c) (hb : Blocks n r m q b) : Blocks n r m q c := by
  obtain ⟨D,hD,hd⟩ := hb
  refine ⟨D,hD,?_⟩
  have hh := dvd_mul_of_dvd_right hbc D
  have heq : (D*b-q)-D*(b-c)=D*c-q := by ring
  simpa only [heq] using dvd_sub hd hh

private theorem unit_eq_of_dvd {r u v : ℕ}
    (hu : u ∈ units r) (hv : v ∈ units r)
    (hd : (r:ℤ) ∣ (u:ℤ)-v) : u=v := by
  have hh := (Nat.modEq_iff_dvd.mpr hd).symm
  change u%r=v%r at hh
  simpa [Nat.mod_eq_of_lt (mem_units.mp hu).1,
    Nat.mod_eq_of_lt (mem_units.mp hv).1] using hh



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
open LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits

/-- With at most `ell` insertions, a unique second-fastest repair can cover a
full primitive period only when its faster insertion has half-integer phase.
The returned primitive boundary also certifies that this fast band is active. -/
theorem solution {n r m Q ell : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hfull : n ≤ m*(n-r))
    (hP : m*r ∈ W) (hQ : Q ∈ W) (hpq : m*r < Q)
    (hWpos : ∀ q ∈ W, 0 < q)
    (hslow : ∀ q ∈ (W.erase (m*r)).erase Q, q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬r ∣ q)
    (hell : 3 ≤ ell) (hcard : W.card ≤ ell)
    (hphi : 2*ell-2 ≤ r.totient)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    (r ∣ 2*Q) ∧ ∃ b ∈ primitiveFlanks n r,
      Blocks (n:ℤ) r m Q b := by
  classical
  have hr : 1 < r := by omega
  have hri : (0:ℤ) < r := by omega
  have hrni : (r:ℤ) < n := by exact_mod_cast hrn
  have hmi : (0:ℤ) < m := by omega
  let T := W.erase (m*r)
  let L := T.erase Q
  let B := fun q : ℕ => (units r).filter (fun u : ℕ => Blocks (n:ℤ) r m q (u:ℤ))
  have hQT : Q ∈ T := Finset.mem_erase.mpr ⟨by omega,hQ⟩
  have hcover : ∀ u ∈ units r, ∃ q ∈ T, u ∈ B q := by
    intro u hu
    obtain ⟨b,hbl,hbu,hbc,hmod⟩ := lift_unit hlarge hrn hu
    obtain ⟨q,hq,D,hD,hd⟩ := FastestBoundary.failed_unit_has_determinant
      hn hrR hlarge hrn hm hbl (lt_of_lt_of_le hbu hfull) hbc hno
    have hbu' : (r:ℤ) ∣ (b:ℤ)-u := by
      apply Nat.modEq_iff_dvd.mp
      change u%r=b%r
      rw [hmod, Nat.mod_eq_of_lt (mem_units.mp hu).1]
    exact ⟨q,hq,Finset.mem_filter.mpr ⟨hu,
      blocks_of_dvd_sub hbu' ⟨D,hD,hd⟩⟩⟩
  have hcap : ∀ q ∈ L, (B q).card ≤ 1 := by
    intro q hq
    have hqT : q ∈ T := (Finset.mem_erase.mp hq).2
    have hqW : q ∈ W := (Finset.mem_erase.mp hqT).2
    apply slower_blocker_card (q:=(q:ℤ)) (B q) (fun u : ℕ => (u:ℤ)) hri hrni hmi
      (by exact_mod_cast hWpos q hqW) (by exact_mod_cast hslow q hq)
      (by exact_mod_cast hunique q hqT)
    · intro u hu v hv hd
      exact unit_eq_of_dvd (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hv).1 hd
    · intro u hu
      exact (Finset.mem_filter.mp hu).2
  have hcount : r.totient ≤ L.card+(B Q).card := by
    have hsub : units r ⊆ (L.biUnion B) ∪ B Q := by
      intro u hu
      obtain ⟨q,hq,hqu⟩ := hcover u hu
      by_cases hqQ : q=Q
      · subst q
        exact Finset.mem_union_right _ hqu
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨q,Finset.mem_erase.mpr ⟨hqQ,hq⟩,hqu⟩)
    calc
      r.totient = (units r).card := rfl
      _ ≤ ((L.biUnion B) ∪ B Q).card := Finset.card_le_card hsub
      _ ≤ (L.biUnion B).card+(B Q).card := Finset.card_union_le _ _
      _ ≤ (∑ q ∈ L, (B q).card)+(B Q).card :=
        Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ (∑ _q ∈ L, 1)+(B Q).card :=
        Nat.add_le_add_right (Finset.sum_le_sum hcap) _
      _ = L.card+(B Q).card := by simp
  have hLc : L.card+2=W.card := by
    have ht := Finset.card_erase_add_one hP
    have hl := Finset.card_erase_add_one hQT
    dsimp [L,T] at *
    omega
  have hnotcop : ¬IsCoprime (r:ℤ) Q := by
    intro hcop
    have htwo : (B Q).card ≤ 2 := by
      apply coprime_blocker_card (B Q) (fun u : ℕ => (u:ℤ)) hri hrni hmi hcop
      · intro u hu v hv hd
        exact unit_eq_of_dvd (Finset.mem_filter.mp hu).1
          (Finset.mem_filter.mp hv).1 hd
      · intro u hu
        exact (Finset.mem_filter.mp hu).2
    omega
  have hhalf : r.totient < 2*(B Q).card := by omega
  have hB : B Q ⊆ units r := Finset.filter_subset _ _
  obtain ⟨u,hu,hopp⟩ := exists_opposite_pair hr hB hhalf
  have huu := hB hu
  have hopu := hB hopp
  have hdiv : (r:ℤ) ∣ 2*(Q:ℤ) := by
    apply opposite_blocks_dvd_twice hri hrni hmi hnotcop
      (Nat.isCoprime_iff_coprime.mpr (mem_units.mp huu).2)
      (Nat.isCoprime_iff_coprime.mpr (mem_units.mp hopu).2)
    · have hsum : (u:ℤ)+(r-u:ℕ)=r := by
        rw [Nat.cast_sub (mem_units.mp huu).1.le]
        ring
      rw [hsum]
    · exact (Finset.mem_filter.mp hu).2
    · exact (Finset.mem_filter.mp hopp).2
  refine ⟨by exact_mod_cast hdiv,?_⟩
  obtain ⟨b,hbl,hbu,hbc,hmod⟩ := lift_unit hlarge hrn huu
  refine ⟨b,mem_primitiveFlanks.mpr ⟨hbl,hbu,hbc⟩,?_⟩
  apply blocks_of_dvd_sub (b:=(u:ℤ))
  · apply dvd_neg.mp
    have hh : (r:ℤ) ∣ (b:ℤ)-u := by
      apply Nat.modEq_iff_dvd.mp
      change u%r=b%r
      rw [hmod, Nat.mod_eq_of_lt (mem_units.mp huu).1]
    simpa only [neg_sub] using hh
  · exact (Finset.mem_filter.mp hu).2
