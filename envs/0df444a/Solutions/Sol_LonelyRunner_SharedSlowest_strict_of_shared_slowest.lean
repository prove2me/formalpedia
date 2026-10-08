-- Prove2me | solution 1 for LonelyRunner.SharedSlowest.strict_of_shared_slowest
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:23:10.148006+00:00
-- url     : https://prove2.me/submissions/4216aee8-7052-4814-985c-9ab223fdc1cf

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_CollectiveFibreNormalForm_activeFibre_of_blocks
import Theorems.Thm_LonelyRunner_FastestBoundary_boundary_blocker
import Theorems.Thm_LonelyRunner_SharedSlowest_strict_of_complementary
import Theorems.Thm_LonelyRunner_SharedSlowestHalf_strict_of_half_and_nonhalf
import Theorems.Thm_LonelyRunner_SharedSlowestHalf_strict_of_two_half

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





















end LonelyRunner.CollectiveUnits

namespace LonelyRunner.CollectiveFibreNormalForm





end LonelyRunner.CollectiveFibreNormalForm

namespace LonelyRunner.CollectiveFibreCounting
open CollectiveUnits

/-- A surjective homomorphism of finite groups has equally sized fibres. -/
theorem card_fibre_mul_card {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (c : H) :
    (Finset.univ.filter (fun g => f g=c)).card * Fintype.card H = Fintype.card G := by
  classical
  have hh : ∀ x : H, (Finset.univ.filter (fun g => f g=x)).card =
      (Finset.univ.filter (fun g => f g=c)).card := by
    intro x
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf c)
  have hc := Finset.card_eq_sum_card_fiberwise
    (s:=Finset.univ) (t:=Finset.univ) (f:=f) (by simp)
  simp only [Finset.card_univ] at hc
  rw [Finset.sum_congr rfl (fun x _ => hh x)] at hc
  simpa [Nat.mul_comm] using hc.symm

/-- Unit-valued reduction has the exact expected fibre cardinality. -/
theorem reduction_fibre_card {r h : ℕ} [NeZero r] [NeZero h]
    (hd : h ∣ r) (c : (ZMod h)ˣ) :
    (Finset.univ.filter (fun u : (ZMod r)ˣ => ZMod.unitsMap hd u=c)).card * h.totient =
      r.totient := by
  classical
  simpa only [ZMod.card_units_eq_totient] using
    card_fibre_mul_card (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) c

/-- Counting units by their natural representatives preserves any predicate. -/
theorem card_unit_filter {r : ℕ} [NeZero r]
    (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun u : (ZMod r)ˣ => p (u : ZMod r).val)).card =
      ((units r).filter p).card := by
  classical
  apply Finset.card_bij (fun (u : (ZMod r)ˣ) _ => (u : ZMod r).val)
  · intro u hu
    obtain ⟨_,hp⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨mem_units.mpr
      ⟨ZMod.val_lt _,(ZMod.val_coe_unit_coprime u).symm⟩,hp⟩
  · intro u _ v _ heq
    apply Units.ext
    exact ZMod.val_injective r heq
  · intro b hb
    obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbr,hcop⟩ := mem_units.mp hb
    refine ⟨ZMod.unitOfCoprime b hcop.symm,?_,?_⟩
    · simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hbr] using hp
    · simp [ZMod.val_natCast, Nat.mod_eq_of_lt hbr]

private theorem unitsMap_natCast {r h : ℕ} [NeZero r] [NeZero h]
    (hd : h ∣ r) (u : (ZMod r)ˣ) :
    (ZMod.unitsMap hd u : ZMod h) = ((u : ZMod r).val : ZMod h) := by
  rw [ZMod.unitsMap_val, ← ZMod.natCast_zmod_val (u : ZMod r)]
  simp

/-- A coprime linear congruence occupies exactly one reduction fibre. -/
theorem congruence_fibre_card {r h U V : ℕ} (hr : 0<r) (hh : 0<h)
    (hd : h ∣ r) (hU : Nat.Coprime h U) (hV : Nat.Coprime h V) :
    ((units r).filter (fun b : ℕ => (h:ℤ) ∣ (V:ℤ)*b-U)).card * h.totient = r.totient := by
  classical
  let : NeZero r := ⟨by omega⟩
  let : NeZero h := ⟨by omega⟩
  let v : (ZMod h)ˣ := ZMod.unitOfCoprime V hV.symm
  let w : (ZMod h)ˣ := ZMod.unitOfCoprime U hU.symm
  have heq : ∀ x : (ZMod r)ˣ,
      ((h:ℤ) ∣ (V:ℤ)*(x : ZMod r).val-U) ↔ ZMod.unitsMap hd x=v⁻¹*w := by
    intro x
    rw [eq_inv_mul_iff_mul_eq]
    rw [Units.ext_iff]
    simp only [Units.val_mul, unitsMap_natCast, v, w, ZMod.coe_unitOfCoprime]
    rw [← sub_eq_zero]
    norm_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
  have hfilters : (Finset.univ.filter (fun x : (ZMod r)ˣ =>
      (h:ℤ) ∣ (V:ℤ)*(x : ZMod r).val-U)) =
      Finset.univ.filter (fun x => ZMod.unitsMap hd x=v⁻¹*w) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq]
  rw [← card_unit_filter (fun b : ℕ => (h:ℤ) ∣ (V:ℤ)*b-U), hfilters]
  exact reduction_fibre_card hd (v⁻¹*w)

end LonelyRunner.CollectiveFibreCounting

namespace LonelyRunner.TotientCapacity

private theorem prime_power_bounds (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    p^k ≤ 2*(p^k).totient^2 ∧ (Odd (p^k) → p^k ≤ (p^k).totient^2) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.totient_prime_pow_succ hp]
  have hp2 := hp.two_le
  have hp1 : p-1+1=p := Nat.sub_add_cancel (by omega)
  have hx : 1 ≤ p^j := Nat.one_le_pow j p (by omega)
  have hxx : p^j ≤ (p^j)^2 := by nlinarith
  have htwo : p ≤ 2*(p-1)^2 := by nlinarith
  constructor
  · have hmul := Nat.mul_le_mul hxx htwo
    simpa [pow_succ, mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  · intro hodd
    have hpodd : Odd p := (Nat.odd_pow_iff (Nat.succ_ne_zero j)).mp hodd
    have hp3 : 3 ≤ p := by
      have := Nat.odd_iff.mp hpodd
      omega
    have hone : p ≤ (p-1)^2 := by nlinarith
    have hmul := Nat.mul_le_mul hxx hone
    simpa [pow_succ, mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- The elementary bound `phi(n)^2 ≥ n/2`, with the stronger odd case. -/
theorem totient_square_bounds (n : ℕ) :
    n ≤ 2*n.totient^2 ∧ (Odd n → n ≤ n.totient^2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk => exact prime_power_bounds p k hp hk
  | coprime a b _ _ hcop ha hb =>
    rw [Nat.totient_mul hcop, mul_pow]
    have hodd : Odd a ∨ Odd b := by
      by_contra! hh
      have hae : Even a := (Nat.even_or_odd a).resolve_right hh.1
      have hbe : Even b := (Nat.even_or_odd b).resolve_right hh.2
      have hd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd hae.two_dvd hbe.two_dvd
      rw [hcop] at hd
      norm_num at hd
    constructor
    · rcases hodd with hao | hbo
      · have hh := Nat.mul_le_mul (ha.2 hao) hb.1
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
      · have hh := Nat.mul_le_mul ha.1 (hb.2 hbo)
        simpa [Nat.mul_assoc] using hh
    · intro hab
      obtain ⟨hao,hbo⟩ := Nat.odd_mul.mp hab
      exact Nat.mul_le_mul (ha.2 hao) (hb.2 hbo)

theorem le_two_totient_sq (n : ℕ) : n ≤ 2*n.totient^2 :=
  (totient_square_bounds n).1



end LonelyRunner.TotientCapacity

namespace LonelyRunner.SmallTotient

/-- Every integer at least seven has at least four unit residues. -/
theorem four_le_totient {r : ℕ} (hr : 7 ≤ r) : 4 ≤ r.totient := by
  by_contra h
  have hphi : r.totient ≤ 3 := by omega
  have hsq := Nat.pow_le_pow_left hphi 2
  have hbound := TotientCapacity.le_two_totient_sq r
  have hrbound : r < 19 := by nlinarith only [hbound, hsq]
  have hfinite : ∀ a : Fin 19, 7 ≤ a.val → 4 ≤ a.val.totient := by decide
  exact h (hfinite ⟨r, hrbound⟩ hr)

/-- An odd integer at least seven has at least six unit residues. -/
theorem six_le_totient_of_odd {r : ℕ} (hr : 7 ≤ r) (hodd : Odd r) :
    6 ≤ r.totient := by
  by_contra h
  have hphi : r.totient ≤ 5 := by omega
  have hsq := Nat.pow_le_pow_left hphi 2
  have hbound := TotientCapacity.le_two_totient_sq r
  have hrbound : r < 51 := by nlinarith only [hbound, hsq]
  have hfinite : ∀ a : Fin 51, 7 ≤ a.val → Odd a.val → 6 ≤ a.val.totient := by
    decide
  exact h (hfinite ⟨r, hrbound⟩ hr hodd)

/-- The only moduli above two with at most two units are 3, 4 and 6. -/
theorem eq_three_four_six {h : ℕ} (hh : 2 < h) (hphi : h.totient ≤ 2) :
    h = 3 ∨ h = 4 ∨ h = 6 := by
  have hsq := Nat.pow_le_pow_left hphi 2
  have hbound := TotientCapacity.le_two_totient_sq h
  have hhbound : h < 9 := by nlinarith only [hbound, hsq]
  have hfinite : ∀ a : Fin 9, 2 < a.val → a.val.totient ≤ 2 →
      a.val = 3 ∨ a.val = 4 ∨ a.val = 6 := by decide
  exact hfinite ⟨h, hhbound⟩ hh hphi



end LonelyRunner.SmallTotient

namespace LonelyRunner.CollectiveFibreClassification
open CollectiveBoundary CollectiveUnits



@[simp] theorem mem_badUnits {n r m q b : ℕ} :
    b ∈ badUnits n r m q ↔ b ∈ units r ∧ Blocks (n:ℤ) r m q b := by
  classical
  simp [badUnits]

private theorem unit_eq_of_dvd {r u v : ℕ}
    (hu : u ∈ units r) (hv : v ∈ units r)
    (hd : (r:ℤ) ∣ (u:ℤ)-v) : u=v := by
  have hh := (Nat.modEq_iff_dvd.mpr hd).symm
  change u%r=v%r at hh
  simpa [Nat.mod_eq_of_lt (mem_units.mp hu).1,
    Nat.mod_eq_of_lt (mem_units.mp hv).1] using hh

/-- For an even modulus a coprime blocker has only one contributing determinant. -/
theorem even_coprime_capacity {n r m q : ℕ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (heven : Even r)
    (hq : Nat.Coprime r q) : (badUnits n r m q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro b hb c hc
  obtain ⟨hb,D,hD,hd⟩ := mem_badUnits.mp hb
  obtain ⟨hc,E,hE,he⟩ := mem_badUnits.mp hc
  have hqi : IsCoprime (r:ℤ) q := Nat.isCoprime_iff_coprime.mpr hq
  have hDi := determinant_coprime hqi hd
  have hEi := determinant_coprime hqi he
  have hr2 : (2:ℤ) ∣ r := by exact_mod_cast heven.two_dvd
  obtain ⟨d,hdodd⟩ := Int.isCoprime_two_left.mp (hDi.of_isCoprime_of_dvd_left hr2)
  obtain ⟨e,heodd⟩ := Int.isCoprime_two_left.mp (hEi.of_isCoprime_of_dvd_left hr2)
  have hclose := abs_le.mp (candidate_close (by exact_mod_cast hr)
    (by exact_mod_cast hrn) (by exact_mod_cast hm) hD hE)
  have hDE : D=E := by omega
  have he' : (r:ℤ) ∣ D*c-q := by rw [hDE]; exact he
  exact unit_eq_of_dvd hb hc (same_det_residue_of_coprime hqi hd he')

/-- A coprime blocker occupies strictly less than half the units when r>=7. -/
theorem coprime_capacity_strict {n r m q : ℕ}
    (hr : 7 ≤ r) (hrn : r < n) (hm : 0 < m) (hq : Nat.Coprime r q) :
    2*(badUnits n r m q).card < r.totient := by
  classical
  rcases Nat.even_or_odd r with heven | hodd
  · have hc := even_coprime_capacity (by omega) hrn hm heven hq
    have hphi := SmallTotient.four_le_totient hr
    omega
  · have hc : (badUnits n r m q).card ≤ 2 := by
      apply coprime_blocker_card (n:=(n:ℤ)) (m:=(m:ℤ)) (badUnits n r m q) (fun b : ℕ => (b:ℤ))
        (by exact_mod_cast (show 0<r by omega)) (by exact_mod_cast hrn)
        (by exact_mod_cast hm) (Nat.isCoprime_iff_coprime.mpr hq)
      · intro b hb c hc hd
        exact unit_eq_of_dvd (mem_badUnits.mp hb).1 (mem_badUnits.mp hc).1 hd
      · intro b hb
        exact (mem_badUnits.mp hb).2
    have hphi := SmallTotient.six_le_totient_of_odd hr hodd
    omega

/-- A blocker outside the half-phase resonance covers at most half the units. -/
theorem nonhalf_capacity {n r m q : ℕ}
    (hr : 7 ≤ r) (hrn : r < n) (hm : 0 < m) (hhalf : ¬r ∣ 2*q) :
    2*(badUnits n r m q).card ≤ r.totient := by
  classical
  by_cases hcop : Nat.Coprime r q
  · exact (coprime_capacity_strict hr hrn hm hcop).le
  · apply no_opposite_half_card (by omega)
      (show badUnits n r m q ⊆ units r from fun b hb => (mem_badUnits.mp hb).1)
    intro b hb hc
    have hbu := (mem_badUnits.mp hb).1
    have hcu := (mem_badUnits.mp hc).1
    apply hhalf
    have hdi : (r:ℤ) ∣ 2*(q:ℤ) := by
      apply opposite_blocks_dvd_twice (n:=(n:ℤ)) (m:=(m:ℤ)) (by exact_mod_cast (show 0<r by omega))
        (by exact_mod_cast hrn) (by exact_mod_cast hm)
        (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
        (Nat.isCoprime_iff_coprime.mpr (mem_units.mp hbu).2)
        (Nat.isCoprime_iff_coprime.mpr (mem_units.mp hcu).2)
      · have heq : (b:ℤ)+(r-b:ℕ)=r := by
          rw [Nat.cast_sub (mem_units.mp hbu).1.le]
          ring
        rw [heq]
      · exact (mem_badUnits.mp hb).2
      · exact (mem_badUnits.mp hc).2
    exact_mod_cast hdi

/-- Two proper boundary blockers in a complete cover are noncoprime and each
occupies exactly half the unit group. -/
theorem cover_forces_half_cards {n r m q u : ℕ}
    (hr : 7 ≤ r) (hrn : r < n) (hm : 0 < m)
    (hq : ¬r ∣ 2*q) (hu : ¬r ∣ 2*u)
    (hcover : ∀ b ∈ units r, Blocks (n:ℤ) r m q b ∨ Blocks (n:ℤ) r m u b) :
    ¬Nat.Coprime r q ∧ ¬Nat.Coprime r u ∧
    2*(badUnits n r m q).card=r.totient ∧
    2*(badUnits n r m u).card=r.totient ∧
    Disjoint (badUnits n r m q) (badUnits n r m u) := by
  classical
  have hcapq := nonhalf_capacity hr hrn hm hq
  have hcapu := nonhalf_capacity hr hrn hm hu
  have hunion : badUnits n r m q ∪ badUnits n r m u = units r := by
    ext b
    simp only [Finset.mem_union, mem_badUnits]
    exact ⟨fun h => h.elim And.left And.left,
      fun hb => (hcover b hb).elim (fun hh => Or.inl ⟨hb,hh⟩) (fun hh => Or.inr ⟨hb,hh⟩)⟩
  have hcount := Finset.card_union_le (badUnits n r m q) (badUnits n r m u)
  rw [hunion,card_units] at hcount
  have heqq : 2*(badUnits n r m q).card=r.totient := by omega
  have hequ : 2*(badUnits n r m u).card=r.totient := by omega
  refine ⟨?_,?_,heqq,hequ,?_⟩
  · intro hcop
    have := coprime_capacity_strict hr hrn hm hcop
    omega
  · intro hcop
    have := coprime_capacity_strict hr hrn hm hcop
    omega
  · apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    have hc := Finset.card_union_add_card_inter (badUnits n r m q) (badUnits n r m u)
    rw [hunion,card_units] at hc
    omega

/-- The normal form's congruence is one complete unit-reduction fibre. -/
theorem active_card {n r m q : ℕ} (hr : 0 < r)
    (F : CollectiveFibreNormalForm.ActiveFibre n r m q) :
    (badUnits n r m q).card * F.h.totient = r.totient := by
  classical
  have heq : badUnits n r m q = (units r).filter
      (fun b : ℕ => (F.h:ℤ) ∣ (F.V:ℤ)*b-F.U) := by
    ext b
    simp only [mem_badUnits, Finset.mem_filter]
    exact and_congr_right (fun hb => F.blocks_iff b hb)
  rw [heq]
  exact CollectiveFibreCounting.congruence_fibre_card hr (by have := F.h_two; omega)
    (⟨F.d, by nlinarith only [F.r_eq]⟩) F.copU F.copV

/-- Every active proper half-sized fibre has quotient 3, 4, or 6. -/
theorem small_quotient {n r m q : ℕ} (hr : 7 ≤ r)
    (hq : ¬r ∣ 2*q) (F : CollectiveFibreNormalForm.ActiveFibre n r m q)
    (hcard : 2*(badUnits n r m q).card = r.totient) :
    F.h=3 ∨ F.h=4 ∨ F.h=6 := by
  have hc := active_card (by omega : 0 < r) F
  have hphi := SmallTotient.four_le_totient hr
  have hpos : 0 < (badUnits n r m q).card := by omega
  have heq : F.h.totient=2 := by nlinarith
  have hh : 2 < F.h := by
    have ht := F.h_two
    by_contra! hh
    have hh2 : F.h=2 := by omega
    apply hq
    refine ⟨F.U, ?_⟩
    have hr2 : r=F.d*2 := F.r_eq.trans (by rw [hh2])
    calc
      2*q=2*(F.d*F.U) := congrArg (2 * ·) F.q_eq
      _=(F.d*2)*F.U := by ring
      _=r*F.U := by rw [← hr2]
  exact SmallTotient.eq_three_four_six hh heq.le

/-- A complete cover by two non-half-phase blockers forces two complementary
small quotient fibres, with their actual determinant windows included. -/
theorem complementary_fibres {n r m q u : ℕ}
    (hr : 7 ≤ r) (hrn : r < n) (hm : 0 < m)
    (hpq : m*r < q) (hpu : m*r < u)
    (hq : ¬r ∣ 2*q) (hu : ¬r ∣ 2*u)
    (hcover : ∀b ∈ units r, Blocks (n:ℤ) r m q b ∨ Blocks (n:ℤ) r m u b) :
    ∃F : CollectiveFibreNormalForm.ActiveFibre n r m q,
    ∃G : CollectiveFibreNormalForm.ActiveFibre n r m u,
      (F.h=3 ∨ F.h=4 ∨ F.h=6) ∧ (G.h=3 ∨ G.h=4 ∨ G.h=6) ∧
      ∀b ∈ units r, Blocks (n:ℤ) r m u b → ¬Blocks (n:ℤ) r m q b := by
  classical
  obtain ⟨hqc,huc,hqcard,hucard,hdis⟩ := cover_forces_half_cards hr hrn hm hq hu hcover
  have hphi := SmallTotient.four_le_totient hr
  have hqa : ∃b ∈ units r, Blocks (n:ℤ) r m q b := by
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (badUnits n r m q).card by omega)
    exact ⟨b,mem_badUnits.mp hb⟩
  have hua : ∃b ∈ units r, Blocks (n:ℤ) r m u b := by
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (badUnits n r m u).card by omega)
    exact ⟨b,mem_badUnits.mp hb⟩
  obtain ⟨F⟩ := CollectiveFibreNormalForm.activeFibre_of_blocks (by omega : 0 < r)
    hrn hm hpq (fun hh => hq (dvd_mul_of_dvd_right hh 2)) hqc hqa
  obtain ⟨G⟩ := CollectiveFibreNormalForm.activeFibre_of_blocks (by omega : 0 < r)
    hrn hm hpu (fun hh => hu (dvd_mul_of_dvd_right hh 2)) huc hua
  refine ⟨F,G,small_quotient hr hq F hqcard,small_quotient hr hu G hucard,?_⟩
  intro b hb hbu hbq
  exact Finset.disjoint_left.mp hdis (mem_badUnits.mpr ⟨hb,hbq⟩)
    (mem_badUnits.mpr ⟨hb,hbu⟩)

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

theorem cover_of_no_strict {n r m q u : ℕ} {R : Finset ℕ}
    (hn : 5 ≤ n) (hrn : r < n) (hm : 2 ≤ m) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hfull : n < m*(n-r))
    (hno : ¬SeparatedMulti.HasStrictTime n R {m*r,q,u}) :
    ∀c ∈ units r, Blocks (n:ℤ) r m q c ∨ Blocks (n:ℤ) r m u c := by
  classical
  intro c hc
  obtain ⟨b,hb,hbn,hcop,hmod⟩ := lift_unit hlarge hrn hc
  obtain ⟨v,hv,D,hD,hd⟩ := FastestBoundary.failed_unit_has_determinant hn hrR hlarge
    hrn hm hb (hbn.trans hfull) hcop hno
  have hmodD : (r:ℤ) ∣ (b:ℤ)-c := by
    apply Nat.modEq_iff_dvd.mp
    change c%r=b%r
    rw [hmod,Nat.mod_eq_of_lt (mem_units.mp hc).1]
  have hdc : (r:ℤ) ∣ D*c-v := by
    have heq : (D*(b:ℤ)-v)-D*((b:ℤ)-c)=D*c-v := by ring
    simpa only [heq] using dvd_sub hd (dvd_mul_of_dvd_right hmodD D)
  have hvmem := Finset.mem_of_mem_erase hv
  have hvne := (Finset.mem_erase.mp hv).1
  simp only [Finset.mem_insert,Finset.mem_singleton] at hvmem
  rcases hvmem with hvP | rfl | rfl
  · exact False.elim (hvne hvP)
  · exact Or.inl ⟨D,hD,hdc⟩
  · exact Or.inr ⟨D,hD,hdc⟩

/-- If one blocker is not half-phase, a complete cover forces actual activity
of the other blocker. This also handles an initially inactive arbitrary runner. -/
theorem active_of_other_nonhalf {n r m q u : ℕ}
    (hr : 7 ≤ r) (hrn : r < n) (hm : 0 < m) (hu : ¬r ∣ 2*u)
    (hcover : ∀c ∈ units r, Blocks (n:ℤ) r m q c ∨ Blocks (n:ℤ) r m u c) :
    ∃c ∈ units r, Blocks (n:ℤ) r m q c := by
  classical
  by_contra! hno
  have heq : badUnits n r m u=units r := by
    ext c
    simp only [mem_badUnits]
    exact ⟨And.left,fun hc => ⟨hc,(hcover c hc).resolve_left (hno c hc)⟩⟩
  have hcap := nonhalf_capacity hr hrn hm hu
  rw [heq,card_units] at hcap
  have hphi := SmallTotient.four_le_totient hr
  omega

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
open LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- **Shared slowest repair theorem.** No upper bound on either faster speed
or the multiplier is imposed. The conclusion is a real strict lonely time
for every retained baseline speed and all three insertions. -/
theorem solution {n r s m k q u : ℕ} {R : Finset ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 2 ≤ m) (hk : 0 < k) (hshared : m*r=k*s)
    (hpq : m*r < q) (hqu : q < u) (hnq : ¬r ∣ q) (hnu : ¬r ∣ u) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  have hr0 : 0 < r := by omega
  have hrn : r < n := hrs.trans hsn
  have hrmax : r+2 ≤ n := by omega
  have hm0 : 0 < m := by omega
  have hn : 5 ≤ n := by omega
  have hfull := SharedMiddleArithmetic.shared_full_period hr0 hrs hsn hk hshared
  by_contra hno
  have hcover := CanonicalTwoCover.cover_of_no_strict hn hrn hm hrR hlarge hfull hno
  by_cases hqhalf : r ∣ 2*q
  · by_cases huhalf : r ∣ 2*u
    · exact hno (SharedSlowestHalf.strict_of_two_half hr hrmax hm0 hrR hlarge hfull
        hpq hqu hqhalf huhalf hnq hnu)
    · obtain ⟨b,hb,hbq⟩ := CanonicalTwoCover.active_of_other_nonhalf hr hrn hm0 huhalf hcover
      have hband := half_phase_band_of_block (by omega : 0 < n) hr0 hm0 hqhalf hnq
        (mem_units.mp hb).2 hbq
      exact hno (SharedSlowestHalf.strict_of_half_and_nonhalf hr hrmax hm0 hrR hlarge hfull
        hpq hqhalf hnq huhalf hband)
  · by_cases huhalf : r ∣ 2*u
    · have hcover' := fun b hb => (hcover b hb).symm
      obtain ⟨b,hb,hbu⟩ := CanonicalTwoCover.active_of_other_nonhalf hr hrn hm0 hqhalf hcover'
      have hband := half_phase_band_of_block (by omega : 0 < n) hr0 hm0 huhalf hnu
        (mem_units.mp hb).2 hbu
      have ht := SharedSlowestHalf.strict_of_half_and_nonhalf hr hrmax hm0 hrR hlarge hfull
        (hpq.trans hqu) huhalf hnu hqhalf hband
      apply hno
      simpa only [Finset.pair_comm u q] using ht
    · obtain ⟨F,G,hF,hG,hcomp⟩ := CollectiveFibreClassification.complementary_fibres
        hr hrn hm0 hpq (hpq.trans hqu) hqhalf huhalf hcover
      exact hno (strict_of_complementary F G hr hlarge hrs hsn hrR hm0 hk hshared
        hpq hqu hF hG hcomp)
