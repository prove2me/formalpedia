-- Prove2me | solution 1 for LonelyRunner.MixedNormalize.normalize
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:32.414901+00:00
-- url     : https://prove2.me/submissions/28be9bdd-7b1a-4c0f-a89d-ac9b1ebcfdd2

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















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

/-- A positive multiplicative interval of ratio p contains a power of p. -/
theorem power_in_window {c p : ℕ} (hc : 0 < c) (hp : 2 ≤ p) :
    ∃ j : ℕ, c ≤ p^j ∧ p^j < p*c := by
  by_cases hc1 : c=1
  · exact ⟨0,by simp [hc1],by simp [hc1]; omega⟩
  have hc2 : 1 < c := by omega
  have hp1 : 1 < p := by omega
  refine ⟨Nat.clog p c,Nat.le_pow_clog hp1 c,?_⟩
  have hh := Nat.mul_lt_mul_of_pos_left (Nat.pow_pred_clog_lt_self hp1 hc2)
    (show 0 < p by omega)
  have hlog := Nat.clog_pos hp1 hc2
  simpa [← pow_succ',Nat.pred_eq_sub_one,Nat.sub_add_cancel (show 1 ≤ Nat.clog p c by omega)] using hh



/-- Every prime at most the multiplier divides the accelerated speed. -/
theorem small_prime_dvd {n s k p : ℕ} (hsn : s < n)
    (hgw : GW n s k) (hp : Nat.Prime p) (hpk : p ≤ k) : p ∣ s := by
  by_contra hnot
  obtain ⟨j,hlo,hhi⟩ := power_in_window (Nat.sub_pos_of_lt hsn) hp.two_le
  apply hgw (p^j) hlo (lt_of_lt_of_le hhi (Nat.mul_le_mul_right (n-s) hpk))
  exact hp.coprime_pow_of_not_dvd hnot

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

/-- Minimality of the first failed unit forces the consecutive normalized
factors ell=d+1. -/
theorem minimal_factor {r s u d ell k c : ℕ}
    (hu : 0 < u) (hc : 0 < c) (hcu : c ≤ u)
    (hrel : s=r+d*u) (hco : Nat.Coprime r (ell*u))
    (hd : d+1 ≤ k) (hsmall : ∀ p, Nat.Prime p → p ≤ k → p ∣ s)
    (hlo : c+d*u ≤ ell*u)
    (hmin : ∀ b, c+d*u ≤ b → Nat.Coprime r b → ell*u ≤ b) : ell=d+1 := by
  have hru : Nat.Coprime r u := (Nat.coprime_mul_iff_right.mp hco).2
  have hrd : Nat.Coprime r (d+1) := by
    by_contra hnot
    obtain ⟨p,hp,hpr,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpk : p ≤ k := le_trans (Nat.le_of_dvd (by omega) hpd) hd
    have hps := hsmall p hp hpk
    have hpdu : p ∣ d*u := by
      have hh := Nat.dvd_sub hps hpr
      simpa [hrel] using hh
    rcases hp.dvd_mul.mp hpdu with hpd0 | hpu
    · have hp1 : p ∣ 1 := by
        have hh := Nat.dvd_sub hpd hpd0
        simpa using hh
      exact hp.not_dvd_one hp1
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hru hpr hpu)
  have hnew : c+d*u ≤ (d+1)*u := by nlinarith
  have hle := hmin ((d+1)*u) hnew (hrd.mul_right hru)
  have hel : ell ≤ d+1 := by nlinarith
  have hde : d+1 ≤ ell := by
    by_contra! hh
    have hmul := Nat.mul_le_mul_right u (show ell ≤ d by omega)
    omega
  omega









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
open LonelyRunner.MixedNormalize
open SeparatedReplacements SecondUnit GWArithmetic

set_option maxHeartbeats 1500000 in
/-- Normalize the least failed unit using the coprime factors of the near-end
determinant and the faster multiplier. -/
theorem solution {n r s m k B D : ℕ}
    (hrs : r < s) (hsn : s < n) (hm : 2 ≤ m) (hD2 : 2 ≤ D)
    (hnear : m*D < k+m) (hgw : GW n s k)
    (hDB : D*B=k*(s-r)) (hBkc : k*(n-s) ≤ B)
    (hBlo : n-r ≤ B) (hBcop : Nat.Coprime r B)
    (hmin : ∀ b, n-r ≤ b → Nat.Coprime r b → B ≤ b) :
    ∃ e d u : ℕ, 0 < e ∧ 0 < d ∧ 0 < u ∧ D=e*d ∧ k=e*(d+1) ∧
      B=(d+1)*u ∧ s=r+d*u ∧ Nat.Coprime u s ∧ k*(n-s) ≤ u := by
  have hD : 0 < D := by omega
  have hmk : m < k := by nlinarith
  have hk : 0 < k := by omega
  have hDk : D < k := by
    nlinarith [Nat.mul_le_mul_right (D-1) hm,show D-1+1=D by omega]
  let e := Nat.gcd D k
  let d := D/e
  let ell := k/e
  have he : 0 < e := Nat.gcd_pos_of_pos_left k hD
  have hDe : D=e*d := (Nat.mul_div_cancel' (Nat.gcd_dvd_left D k)).symm
  have hke : k=e*ell := (Nat.mul_div_cancel' (Nat.gcd_dvd_right D k)).symm
  have hd : 0 < d := by nlinarith
  have hell : 0 < ell := by nlinarith
  have hcop : Nat.Coprime d ell := Nat.coprime_div_gcd_div_gcd he
  have hcancel : d*B=ell*(s-r) := by
    apply Nat.mul_left_cancel he
    nlinarith only [hDB,hDe,hke,
      congrArg (fun z => z*B) hDe,congrArg (fun z => z*(s-r)) hke]
  have hellB : ell ∣ B := hcop.symm.dvd_of_dvd_mul_left
    (by rw [hcancel]; exact dvd_mul_right ell (s-r))
  obtain ⟨u,hBu⟩ := hellB
  have hBpos : 0 < B := by omega
  have hu : 0 < u := by nlinarith
  have hsr : s=r+d*u := by
    have hh : d*u=s-r := by
      apply Nat.mul_left_cancel hell
      nlinarith only [hcancel,congrArg (fun z => d*z) hBu]
    omega
  have hru : Nat.Coprime r u := (Nat.coprime_mul_iff_right.mp (hBu ▸ hBcop)).2
  have hus : Nat.Coprime u s := by
    rw [hsr,Nat.coprime_add_mul_right_right]
    exact hru.symm
  have huc : n-s ≤ u := by
    have he1 : 1 ≤ e := he
    have hmul := Nat.mul_le_mul_right (ell*(n-s)) he1
    have hbound : ell*(n-s) ≤ ell*u := by
      nlinarith only [hBkc,hBu,hke,hmul, congrArg (fun z => z*(n-s)) hke]
    nlinarith
  have hku : k*(n-s) ≤ u := by
    by_contra! hh
    exact hgw u huc hh hus.symm
  have hdell : d < ell := by
    by_contra! hh
    have hh' := Nat.mul_le_mul_left e hh
    omega
  have helk : ell ≤ k := by nlinarith
  have hmin' : ∀ b, (n-s)+d*u ≤ b → Nat.Coprime r b → ell*u ≤ b := by
    intro b hb hcopb
    rw [← hBu]
    exact hmin b (by omega) hcopb
  have hel : ell=d+1 := minimal_factor hu (by omega) huc hsr (hBu ▸ hBcop)
    (by omega) (fun p hp hpk => small_prime_dvd hsn hgw hp hpk) (by omega) hmin'
  exact ⟨e,d,u,he,hd,hu,hDe,by simpa [hel] using hke,by simpa [hel] using hBu,hsr,hus,hku⟩
