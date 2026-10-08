-- Prove2me | solution 1 for LonelyRunner.SharedSlowestHalf.strict_of_two_half
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:20:40.828988+00:00
-- url     : https://prove2.me/submissions/5198cbbe-65d9-43a2-ab2c-461126928022

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset
import Theorems.Thm_LonelyRunner_TwoHalfPhase_strict_before

namespace LonelyRunner













@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]































end LonelyRunner

namespace LonelyRunner.BadCover





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





















@[simp] theorem mem_primitiveFlanks {n r b : ℕ} :
    b ∈ primitiveFlanks n r ↔ n-r ≤ b ∧ b < n ∧ Nat.Coprime r b := by
  simp [primitiveFlanks, and_assoc]

@[simp] theorem card_primitiveFlanks {n r : ℕ} (hrn : r ≤ n) :
    (primitiveFlanks n r).card = r.totient := by
  have heq : n-r+r=n := Nat.sub_add_cancel hrn
  simpa [primitiveFlanks, heq] using Nat.filter_coprime_Ico_eq_totient r (n-r)















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

/-- The half-phase branch of the totient theorem starts at modulus eight. -/
theorem half_phase_modulus_bound {r Q : ℕ}
    (hd : r ∣ 2*Q) (hnot : ¬ r ∣ Q) (hphi : 4 ≤ r.totient) : 8 ≤ r := by
  have heven := even_modulus hd hnot
  by_contra! hsmall
  interval_cases r <;> norm_num at heven
  all_goals revert hphi; decide

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













/-- A primitive flank at least seven indices from the upper endpoint survives
any component whose exit is at most the square of the half-phase stretch. -/
theorem terminal_seven_inequality {n : ℝ} (hn : 8 ≤ n) :
    (n-7)*((n+2)/(n-2))^2 < n+1 := by
  have hd : 0 < n-2 := by linarith
  rw [div_pow, ← mul_div_assoc]
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

/-- The same component exits well before the repair runner's next bad band. -/
theorem half_phase_square_lt_repair_lap {n : ℝ} (hn : 10 ≤ n) :
    ((n+2)/(n-2))^2 < n-1 := by
  have hd : 0 < n-2 := by linarith
  have hz : 0 ≤ (n+2)/(n-2) := by positivity
  have hz2 : (n+2)/(n-2) ≤ 3/2 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  nlinarith

/-- At most three primitive representatives lie in the final six positions
when the modulus is even. -/
theorem terminal_six_discard_card {n r : ℕ} (heven : Even r) :
    ((primitiveFlanks n r).filter (fun b => n-7 < b)).card ≤ 3 := by
  classical
  let S := (primitiveFlanks n r).filter (fun b => n-7 < b)
  have hprop : ∀ b ∈ S, n-7 < b ∧ b<n ∧ b%2=1 := by
    intro b hb
    obtain ⟨hb,hbt⟩ := Finset.mem_filter.mp hb
    obtain ⟨_,hbu,hcop⟩ := mem_primitiveFlanks.mp hb
    have hodd := Nat.coprime_two_left.mp (hcop.of_dvd_left heven.two_dvd)
    exact ⟨hbt,hbu,Nat.odd_iff.mp hodd⟩
  change S.card ≤ 3
  by_contra hh
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd⟩ :=
    Finset.three_lt_card_iff.mp (show 3<S.card by omega)
  have hpa := hprop a ha
  have hpb := hprop b hb
  have hpc := hprop c hc
  have hpd := hprop d hd
  omega

/-- Four units suffice to select a flank surviving the combined bad component. -/
theorem exists_primitive_before_terminal_six {n r : ℕ}
    (hrn : r ≤ n) (heven : Even r) (hphi : 4 ≤ r.totient) :
    ∃ b ∈ primitiveFlanks n r, b ≤ n-7 := by
  classical
  by_contra! hh
  have hsub : primitiveFlanks n r ⊆
      (primitiveFlanks n r).filter (fun b => n-7<b) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨hb,hh b hb⟩
  have hc := (Finset.card_le_card hsub).trans (terminal_six_discard_card heven)
  rw [card_primitiveFlanks hrn] at hc
  omega

/-- Combine the component clock bound with the shared repair's integer margin. -/
theorem flank_survives_square {n b M E : ℝ}
    (hn : 8 ≤ n) (hb0 : 0 ≤ b) (hb : b ≤ n-7)
    (hM : n+1 ≤ M) (hE : E ≤ ((n+2)/(n-2))^2) : b*E < M := by
  have h1 := mul_le_mul_of_nonneg_left hE hb0
  have h2 := mul_le_mul_of_nonneg_right hb (sq_nonneg ((n+2)/(n-2)))
  have h3 := terminal_seven_inequality hn
  linarith

end LonelyRunner.TwoBlockerArithmetic

namespace LonelyRunner.TwoHalfPhase

open TwoBlockerArithmetic













end LonelyRunner.TwoHalfPhase

namespace LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover

/-- Convert a safe normalized clock into a strict time for the actual speeds. -/
theorem strict_of_clock {n r m q u b : ℕ} {R : Finset ℕ} {z : ℝ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hb : b ∈ primitiveFlanks n r)
    (hz : 1 < z) (hzn : z < (n:ℝ)-1)
    (hbz : (b:ℝ)*z < (m:ℝ)*((n:ℝ)-r))
    (hq : 1/(n:ℝ) < ndist ((q:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))))
    (hu : 1/(n:ℝ) < ndist ((u:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r)))) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  classical
  have hn0 : (0:ℝ) < n := by exact_mod_cast lt_trans hr hrn
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  let a := numerator r b
  let clock := (a:ℝ)/r-z/((n:ℝ)*m*r)
  have hP : 1/(n:ℝ) < ndist (((m*r:ℕ):ℝ)*clock) := by
    have heq : ((m*r:ℕ):ℝ)*clock=((m:ℤ)*a:ℤ)-z/(n:ℝ) := by
      dsimp [clock]; push_cast; field_simp
    rw [heq]
    apply strict_of_between (m:=(m:ℤ)*a-1)
    · push_cast
      have hh : z/(n:ℝ) < 1-1/(n:ℝ) := by
        apply (div_lt_iff₀ hn0).mpr
        have he : (1/(n:ℝ))*n=1 := by field_simp
        rw [sub_mul,one_mul,he]
        exact hzn
      linarith
    · push_cast
      have hh : 1/(n:ℝ) < z/(n:ℝ) := (div_lt_div_iff_of_pos_right hn0).mpr hz
      linarith
  refine ⟨clock,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hv
  · exact baseline_clock_safe hr hrn hm hlarge (mem_primitiveFlanks.mp hb).1
      (numerator_unit (mem_primitiveFlanks.mp hb).2.2) (by linarith) hbz hv hvn
      (by rintro rfl; exact hvR hrR)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hP
    · exact hq
    · exact hu





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
open LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover

/-- Two half-phase blockers always leave a strict primitive flank. -/
theorem solution {n r m q u : ℕ} {R : Finset ℕ}
    (hr : 7 ≤ r) (hrmax : r+2 ≤ n) (hm : 0 < m)
    (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hfull : n < m*(n-r))
    (hpq : m*r < q) (hqu : q < u)
    (hq : r ∣ 2*q) (hu : r ∣ 2*u) (hnq : ¬r ∣ q) (hnu : ¬r ∣ u) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  have hr0 : 0 < r := by omega
  have hrn : r < n := by omega
  have hphi := SmallTotient.four_le_totient hr
  have heven := CollectivePhase.even_modulus hq hnq
  have hr8 := CollectivePhase.half_phase_modulus_bound hq hnq hphi
  have hn10 : (10:ℝ) ≤ n := by exact_mod_cast (show 10 ≤ n by omega)
  have hn0 : (0:ℝ) < n := by linarith
  have hr0R : (0:ℝ) < r := by exact_mod_cast hr0
  have hm0R : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨b,hbf,hbsmall⟩ := TwoBlockerArithmetic.exists_primitive_before_terminal_six
    hrn.le heven hphi
  obtain ⟨hb,hbn,hbc⟩ := mem_primitiveFlanks.mp hbf
  have hb0 : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  let Z : ℝ := ((n:ℝ)+2)/((n:ℝ)-2)
  let M : ℝ := (m:ℝ)*((n:ℝ)-r)
  let L : ℝ := min ((n:ℝ)-1) (M/b)
  have hM : (n:ℝ)+1 ≤ M := by
    have ht : n+1 ≤ m*(n-r) := by omega
    have htR : (n:ℝ)+1 ≤ (m:ℝ)*(n-r:ℕ) := by exact_mod_cast ht
    simpa only [Nat.cast_sub hrn.le] using htR
  have hbZ : (b:ℝ)*Z^2 < M := by
    apply TwoBlockerArithmetic.flank_survives_square (by linarith) hb0.le
      (by have hh : (b:ℝ) ≤ (n-7:ℕ) := by exact_mod_cast hbsmall
          simpa only [Nat.cast_sub (by omega : 7 ≤ n),Nat.cast_ofNat] using hh)
      hM le_rfl
  have hZL : Z^2 < L := by
    apply lt_min
    · exact TwoBlockerArithmetic.half_phase_square_lt_repair_lap hn10
    · apply (lt_div_iff₀ hb0).mpr
      nlinarith only [hbZ]
  let slow : ℝ := (q:ℝ)/((m:ℝ)*r)
  let fast : ℝ := (u:ℝ)/((m:ℝ)*r)
  have hslow : 0 < slow := div_pos (by exact_mod_cast (show 0 < q by omega)) (by positivity)
  have horder : slow < fast := div_lt_div_of_pos_right (by exact_mod_cast hqu) (by positivity)
  obtain ⟨z,hz,hqz,huz⟩ := TwoHalfPhase.strict_before hn10 hslow horder hZL
  have hzn := lt_of_lt_of_le hz.2 (min_le_left _ _)
  have hzb := lt_of_lt_of_le hz.2 (min_le_right _ _)
  have hbz : (b:ℝ)*z < M := by
    have hh := (lt_div_iff₀ hb0).mp hzb
    nlinarith only [hh]
  have hunit := numerator_unit hbc
  obtain ⟨J,hJ⟩ := CollectivePhase.half_phase_lap hr0 hq hnq hunit
  obtain ⟨K,hK⟩ := CollectivePhase.half_phase_lap hr0 hu hnu hunit
  apply strict_of_clock hr0 hrn hm hrR hlarge hbf hz.1 hzn hbz
  · have heq : (q:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))=
        (J:ℝ)+(1/2-slow*z/n) := by
      rw [mul_sub,← mul_div_assoc,hJ]
      dsimp [slow]; field_simp; ring
    simpa only [heq,ndist_int_add] using hqz
  · have heq : (u:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))=
        (K:ℝ)+(1/2-fast*z/n) := by
      rw [mul_sub,← mul_div_assoc,hK]
      dsimp [fast]; field_simp; ring
    simpa only [heq,ndist_int_add] using huz
