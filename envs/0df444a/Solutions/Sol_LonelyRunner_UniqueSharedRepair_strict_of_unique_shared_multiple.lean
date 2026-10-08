-- Prove2me | solution 1 for LonelyRunner.UniqueSharedRepair.strict_of_unique_shared_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:25:22.959077+00:00
-- url     : https://prove2.me/submissions/a317855e-1298-40bc-b786-7e4a5d5e9941

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_CollectiveSecondFastest_strict_of_shared_second_fastest
import Theorems.Thm_LonelyRunner_SharedFastest_strict_of_shared_fastest
import Theorems.Thm_LonelyRunner_SharedSlowest_strict_of_shared_slowest

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







































end LonelyRunner.CollectiveUnits

namespace LonelyRunner.CollectiveFibreNormalForm





end LonelyRunner.CollectiveFibreNormalForm

namespace LonelyRunner.CollectiveFibreCounting
open CollectiveUnits











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

/-- **Any-order unique shared repair theorem.** A unique inserted multiple of
a large deletion r>=7, shared with a larger baseline divisor, cannot be tight
when there are at most three positive insertions. -/
theorem strict_of_unique_shared {n r s m k : ℕ} {R W : Finset ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 2 ≤ m) (hk : 0 < k) (hshared : m*r=k*s)
    (hP : m*r ∈ W) (hpos : ∀v ∈ W, 0 < v) (hcard : W.card ≤ 3)
    (hunique : ∀v ∈ W.erase (m*r), ¬r ∣ v) :
    SeparatedMulti.HasStrictTime n R W := by
  classical
  have hn : 5 ≤ n := by omega
  let Q := W.max' ⟨m*r,hP⟩
  have hQ : Q ∈ W := Finset.max'_mem _ _
  have hmax : ∀v ∈ W, v ≤ Q := fun v hv => Finset.le_max' _ _ hv
  have hPQ : m*r ≤ Q := hmax _ hP
  by_cases hQP : Q=m*r
  · apply SharedFastest.strict_of_shared_fastest hn hr hrR hlarge hrs hsn hm hk
      hshared hP hpos ?_ hunique hcard
    intro v hv
    have hvne := (Finset.mem_erase.mp hv).1
    have hvle := hmax v (Finset.mem_of_mem_erase hv)
    omega
  have hpQ : m*r < Q := by omega
  by_cases hmiddle : ∀v ∈ (W.erase (m*r)).erase Q, v < m*r
  · exact CollectiveSecondFastest.strict_of_shared_second_fastest
      (ell:=3) (by decide) hcard hlarge hrs hsn hrR hm hk hshared hP hQ hpQ
      hpos hmiddle (hunique) (by simpa using SmallTotient.four_le_totient hr)
  push Not at hmiddle
  obtain ⟨q,hq,hqP⟩ := hmiddle
  have hqW : q ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
  have hqQ : q ≠ Q := (Finset.mem_erase.mp hq).1
  have hqPne : q ≠ m*r := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hq)).1
  have hPq : m*r < q := by omega
  have hqQlt : q < Q := lt_of_le_of_ne (hmax q hqW) hqQ
  have hnq : ¬r ∣ q := hunique q (Finset.mem_of_mem_erase hq)
  have hnQ : ¬r ∣ Q := hunique Q (Finset.mem_erase.mpr ⟨hQP,hQ⟩)
  have ht := SharedSlowest.strict_of_shared_slowest hr hlarge hrs hsn hrR hm hk hshared
    hPq hqQlt hnq hnQ
  have hsub : ({m*r,q,Q}:Finset ℕ) ⊆ W := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have htriple : ({m*r,q,Q}:Finset ℕ).card=3 := by
    simp [Ne.symm hqPne,Ne.symm hQP,hqQ]
  have hEq : ({m*r,q,Q}:Finset ℕ)=W :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  simpa only [hEq] using ht





end LonelyRunner.UniqueSharedRepair

open LonelyRunner
open LonelyRunner.UniqueSharedRepair

/-- Divisibility-only formulation of the any-order theorem. Positivity and
sharedness themselves supply the positive multipliers and m>=2. -/
theorem solution {n r s P : ℕ} {R W : Finset ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hP : P ∈ W) (hpos : ∀v ∈ W, 0 < v)
    (hcard : W.card ≤ 3) (hrP : r ∣ P) (hsP : s ∣ P)
    (hunique : ∀v ∈ W.erase P, ¬r ∣ v) :
    SeparatedMulti.HasStrictTime n R W := by
  have hPpos := hpos P hP
  obtain ⟨m,hPm⟩ := hrP
  obtain ⟨k,hPk⟩ := hsP
  have hmP : m*r=P := by nlinarith only [hPm]
  have hkP : k*s=P := by nlinarith only [hPk]
  have hm0 : 0 < m := by nlinarith only [hPm,hPpos]
  have hk : 0 < k := by nlinarith only [hPk,hPpos]
  have hm : 2 ≤ m := by
    by_contra! hh
    have hm1 : m=1 := by omega
    have hrP' : r=P := by simpa only [hm1,one_mul] using hmP
    have hsle : s ≤ k*s := Nat.le_mul_of_pos_left s hk
    omega
  apply strict_of_unique_shared hr hlarge hrs hsn hrR hm hk (hmP.trans hkP.symm)
    (by simpa only [hmP] using hP) hpos hcard
  simpa only [hmP] using hunique
