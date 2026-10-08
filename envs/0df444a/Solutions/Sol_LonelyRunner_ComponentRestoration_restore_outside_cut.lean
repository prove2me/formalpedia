-- Prove2me | solution 1 for LonelyRunner.ComponentRestoration.restore_outside_cut
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:57:45.267996+00:00
-- url     : https://prove2.me/submissions/d2e81d05-06e5-4fa3-a26f-5223331c49e5

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_ComponentRestoration_safe_segment
import Theorems.Thm_LonelyRunner_InteractionComponents_localize_interval

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m



















/-- `δ ≤ ‖x‖` iff `x` is at distance at least `δ` from every integer. -/
theorem le_ndist_iff {δ x : ℝ} : δ ≤ ndist x ↔ ∀ m : ℤ, δ ≤ |x - m| :=
  ⟨fun h m => h.trans (ndist_le_abs_sub x m), fun h => h (round x)⟩















end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey











theorem retained_not_dvd {n r v : ℤ} (hr : 0 < r) (hn : n ≤ 2 * r)
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) : ¬ r ∣ v := by
  rintro ⟨k, rfl⟩
  have hk : 0 < k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have : k = 1 := by omega
  simp_all







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

namespace LonelyRunner.InteractionComponents

open Set







theorem same_center_subset {p q : ℕ} {c j : ℤ} {δ : ℝ}
    (hq : 0 < q) (hδ : 0 ≤ δ) (hpq : p ≤ q)
    (hcenter : (q : ℤ)*c-(p : ℤ)*j=0) :
    band δ (q,j) ⊆ band δ (p,c) := by
  intro t ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hcR : (q : ℝ)*c-(p : ℝ)*j=0 := by exact_mod_cast hcenter
  have hid : (q : ℝ)*|(p : ℝ)*t-c| = (p : ℝ)*|(q : ℝ)*t-j| := by
    calc
      _ = |(q:ℝ)*((p:ℝ)*t-c)| := by rw [abs_mul,abs_of_pos hqR]
      _ = |(p:ℝ)*((q:ℝ)*t-j)| := by congr 1; nlinarith only [hcR]
      _ = _ := by rw [abs_mul,abs_of_nonneg hpR]
  change |(q : ℝ)*t-j| ≤ δ at ht
  change |(p : ℝ)*t-c| ≤ δ
  have hmul := mul_le_mul_of_nonneg_left ht hpR
  have hdelta := mul_le_mul_of_nonneg_right hpqR hδ
  nlinarith only [hid,hmul,hdelta,hqR]















end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation

/-- A modular inverse can be represented in any interval of r consecutive integers. -/
theorem unit_representative {n r : ℕ} {a : ℤ}
    (hr : 0 < r) (hrn : r < n) (hc : Int.gcd a r = 1) :
    ∃ b : ℕ, ∃ c : ℤ, n-r ≤ b ∧ b < n ∧ Nat.Coprime r b ∧ a*b-c*r=1 := by
  let s : ℤ := (n:ℤ)-r
  let z : ℤ := Int.gcdA a r
  let k : ℤ := (z-s)/r
  let B : ℤ := s+(z-s)%r
  have hrZ : (0:ℤ) < r := by exact_mod_cast hr
  have hs : (0:ℤ) < s := by dsimp [s]; omega
  have hlo : s ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Int.emod_nonneg _ hrZ.ne')
  have hhi : B < n := by
    have hh := Int.emod_lt_of_pos (z-s) hrZ
    dsimp [B,s] at *
    omega
  have hB : (B.toNat:ℤ)=B := Int.toNat_of_nonneg (by omega)
  have hrel : B+(r:ℤ)*k=z := by
    have hh := Int.emod_add_mul_ediv (z-s) (r:ℤ)
    dsimp [B,k]
    linarith only [hh]
  let c : ℤ := -(a*k+Int.gcdB a r)
  have hdet : a*(B.toNat:ℤ)-c*r=1 := by
    have hh := Int.gcd_eq_gcd_ab a (r:ℤ)
    rw [hc] at hh
    rw [hB]
    dsimp [c,z] at *
    linear_combination a*hrel-hh
  have hcop : IsCoprime (r:ℤ) (B.toNat:ℤ) := by
    exact ⟨-c,a,by nlinarith only [hdet]⟩
  refine ⟨B.toNat,c,?_,?_,?_,hdet⟩
  · have hh : ((n-r:ℕ):ℤ) ≤ B.toNat := by
      rw [hB,Nat.cast_sub hrn.le]
      exact hlo
    exact_mod_cast hh
  · exact_mod_cast (show (B.toNat:ℤ) < n by simpa only [hB] using hhi)
  · simpa only [Int.natAbs_natCast] using Int.isCoprime_iff_nat_coprime.mp hcop

















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents

/-- A bad center at a time safe for the retained baseline must be primitive. -/
theorem primitive_center {n r : ℕ} {D : Finset ℕ} {a : ℤ} {t : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrn : r < n)
    (hD : ∀ d ∈ D, n ≤ 2*d)
    (hsafe : ∀ v : ℕ, 0 < v → v < n → v ∉ D →
      1/(n:ℝ) < ndist ((v:ℝ)*t))
    (hbad : |(r:ℝ)*t-a| ≤ 1/(n:ℝ)) : Int.gcd a r=1 := by
  by_contra hc
  have hg : 0 < Int.gcd a (r:ℤ) :=
    Int.gcd_pos_of_ne_zero_right a (by exact_mod_cast hr.ne')
  obtain ⟨z,x,_hcop,ha,hxr⟩ := Int.exists_gcd_one hg
  have hg2 : (2:ℤ) ≤ Int.gcd a (r:ℤ) := by
    exact_mod_cast (show 2 ≤ Int.gcd a r by omega)
  have hrZ : (0:ℤ) < r := by exact_mod_cast hr
  have hx : 0 < x := by nlinarith [Int.natCast_nonneg (Int.gcd a (r:ℤ))]
  have hx2 : 2*x ≤ r := by nlinarith only [hxr,hg2,hx]
  have hxl : x < r := by omega
  have hxcast : (x.toNat:ℤ)=x := Int.toNat_of_nonneg hx.le
  have hx0 : 0 < x.toNat := by
    exact_mod_cast (show (0:ℤ) < x.toNat by simpa only [hxcast] using hx)
  have hxlt : x.toNat < r := by
    exact_mod_cast (show (x.toNat:ℤ) < r by simpa only [hxcast] using hxl)
  have hx2' : 2*x.toNat ≤ r := by
    exact_mod_cast (show (2:ℤ)*(x.toNat:ℤ) ≤ r by simpa only [hxcast] using hx2)
  have hxD : x.toNat ∉ D := by
    intro hh
    have := hD _ hh
    omega
  have hdet : (r:ℤ)*z-(x.toNat:ℤ)*a=0 := by
    rw [hxcast]
    linear_combination z*hxr-x*ha
  have hsmall := same_center_subset (p := x.toNat) (q := r)
    (c := z) (j := a) hr (by positivity : (0:ℝ) ≤ 1/n) hxlt.le hdet hbad
  exact (not_le_of_gt (hsafe _ hx0 (lt_trans hxlt hrn) hxD))
    ((ndist_le_abs_sub _ z).trans hsmall)

/-- A primitive r-grid center has distance at least 1/r for nonmultiples. -/
theorem primitive_center_bound {r v b : ℕ} {a c : ℤ}
    (hr : 0 < r) (hu : a*(b:ℤ)-c*(r:ℤ)=1) (hnot : ¬ r ∣ v) :
    1/(r:ℝ) ≤ ndist ((v:ℝ)*((a:ℝ)/r)) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [le_ndist_iff]
  intro j
  have hne : (v:ℤ)*a-(r:ℤ)*j ≠ 0 := by
    intro heq
    apply hnot
    have hd : (r:ℤ) ∣ (v:ℤ) := by
      refine ⟨(b:ℤ)*j-c*v,?_⟩
      nlinarith [congrArg (fun x : ℤ => x*v) hu]
    exact_mod_cast hd
  have hunit : (1:ℝ) ≤ |(v:ℝ)*a-(r:ℝ)*j| := by
    exact_mod_cast (show (1:ℤ) ≤ |(v:ℤ)*a-(r:ℤ)*j| by
      have := abs_pos.mpr hne
      omega)
  have hid : |(v:ℝ)*a-(r:ℝ)*j| = r*|(v:ℝ)*((a:ℝ)/r)-j| := by
    calc
      _ = |(r:ℝ)*((v:ℝ)*((a:ℝ)/r)-j)| := by congr 1; field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hrR]
  apply (div_le_iff₀ hrR).mpr
  rw [hid] at hunit
  simpa only [mul_comm] using hunit





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
open LonelyRunner.ComponentRestoration
open SeparatedMulti InteractionComponents

/-- Restore all deletions except D, keeping just a separated cut C of the
insertions. It suffices that each r in D has its smallest repair in C. -/
theorem solution {n : ℕ} {R W D C : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hD : D ⊆ R) (hC : C ⊆ W) (hW : ∀ p ∈ W, 0 < p)
    (hcut : SeparatedCut n W C)
    (hrepair : ∀ r ∈ D, ∃ m : ℕ, 0 < m ∧ m*r ∈ C ∧
      ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hno : ¬ HasStrictTime n R W) : ¬ HasStrictTime n D C := by
  rintro ⟨t,ht⟩
  have hn0 : 0 < n := by omega
  have hret : ∀ v : ℕ, 0 < v → v < n → v ∉ D →
      1/(n:ℝ) < ndist ((v:ℝ)*t) := fun v hv hvn hvD => ht v (Or.inl ⟨hv,hvn,hvD⟩)
  obtain ⟨r,hr,hrk,hrbad⟩ := Real.exists_nat_abs_mul_sub_round_le t
    (show 0 < n-1 by omega)
  have hrn : r < n := by omega
  have hnb : ((n-1:ℕ):ℝ)+1=(n:ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    norm_num
  have hbad : ndist ((r:ℝ)*t) ≤ 1/(n:ℝ) := by
    simpa only [ndist,hnb,mul_comm] using hrbad
  have hrD : r ∈ D := by
    by_contra hh
    exact (not_le_of_gt (hret r hr hrn hh)) hbad
  let a : ℤ := round ((r:ℝ)*t)
  have hband : |(r:ℝ)*t-a| ≤ 1/(n:ℝ) := hbad
  have hprim := primitive_center hn0 hr hrn (fun d hd => (hR d (hD hd)).1) hret hband
  obtain ⟨b,c,_hb,_hbn,_hcop,hu⟩ := GWContactArithmetic.unit_representative hr hrn hprim
  have hlarge := (hR r (hD hrD)).1
  have hsegment : ∀ u ∈ Set.Icc (min t ((a:ℝ)/r)) (max t ((a:ℝ)/r)),
      ∀ v : ℕ, 0 < v → v < n → v ∉ R → 1/(n:ℝ) < ndist ((v:ℝ)*u) := by
    intro u hu' v hv hvn hvR
    have hne : v ≠ r := by rintro rfl; exact hvR (hD hrD)
    have hnot : ¬ r ∣ v := by
      intro hd
      apply Farey.retained_not_dvd (n := (n:ℤ)) (r := (r:ℤ)) (v := (v:ℤ))
        (by exact_mod_cast hr) (by exact_mod_cast hlarge) (by exact_mod_cast hv)
        (by exact_mod_cast hvn) (by exact_mod_cast hne)
      exact_mod_cast hd
    exact safe_segment hn0 hr hrn hvn (primitive_center_bound hr hu hnot) hband
      (hret v hv hvn (fun hvD => hvR (hD hvD))) hu'
  have hcover : ∀ u ∈ Set.Icc (min t ((a:ℝ)/r)) (max t ((a:ℝ)/r)),
      ∃ q ∈ W, ndist ((q:ℝ)*u) ≤ 1/(n:ℝ) := by
    intro u hu'
    by_contra! hh
    apply hno
    refine ⟨u,fun v hv => ?_⟩
    rcases hv with ⟨hv,hvn,hvR⟩ | hvW
    · exact hsegment u hu' v hv hvn hvR
    · exact hh v hvW
  obtain ⟨m,hm,hmC,hmin⟩ := hrepair r hrD
  have hloc := localize_interval hn0 hr hm hC hmC hW hcut hmin hu
    (show (a:ℝ)/r ∈ Set.Icc (min t ((a:ℝ)/r)) (max t ((a:ℝ)/r)) from
      ⟨min_le_right _ _,le_max_right _ _⟩) hcover
  obtain ⟨p,hpC,hpbad⟩ := hloc t ⟨min_le_left _ _,le_max_left _ _⟩
  exact (not_le_of_gt (ht p (Or.inr hpC))) hpbad
