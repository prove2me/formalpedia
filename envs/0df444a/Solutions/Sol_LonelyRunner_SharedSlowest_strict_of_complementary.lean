-- Prove2me | solution 1 for LonelyRunner.SharedSlowest.strict_of_complementary
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:18:39.625578+00:00
-- url     : https://prove2.me/submissions/c821c3e3-47b2-454e-8883-dc53ef07790e

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_ComplementaryEscape_strict_of_surviving_fibre
import Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset
import Theorems.Thm_LonelyRunner_SharedSlowestSmall_strict_before_eight

namespace LonelyRunner















































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



/-- Reduction modulo `r` is injective on one period. -/
theorem primitiveFlanks_mod_injective {n r b c : ℕ}
    (hb : b ∈ primitiveFlanks n r) (hc : c ∈ primitiveFlanks n r)
    (heq : b%r=c%r) : b=c := by
  obtain ⟨hbl,hbu,_⟩ := mem_primitiveFlanks.mp hb
  obtain ⟨hcl,hcu,_⟩ := mem_primitiveFlanks.mp hc
  exact Nat.ModEq.eq_of_abs_lt heq (by rw [abs_lt]; omega)













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







/-- The only integers at least seven with fewer than six units are 8, 10 and 12. -/
theorem eq_eight_ten_twelve {r : ℕ} (hr : 7 ≤ r) (hphi : r.totient < 6) :
    r = 8 ∨ r = 10 ∨ r = 12 := by
  have hphi' : r.totient ≤ 5 := by omega
  have hsq := Nat.pow_le_pow_left hphi' 2
  have hbound := TotientCapacity.le_two_totient_sq r
  have hrbound : r < 51 := by nlinarith only [hbound, hsq]
  have hfinite : ∀ a : Fin 51, 7 ≤ a.val → a.val.totient < 6 →
      a.val = 8 ∨ a.val = 10 ∨ a.val = 12 := by decide
  exact hfinite ⟨r, hrbound⟩ hr hphi

end LonelyRunner.SmallTotient

namespace LonelyRunner.CollectiveFibreClassification
open CollectiveBoundary CollectiveUnits





















end LonelyRunner.CollectiveFibreClassification

namespace LonelyRunner.TwoBlockerGeometry

/-- A band with active centre at least `n/h` has this uniform first-exit bound. -/
theorem active_band_exit_bound {n h T gamma : ℝ}
    (hh : 0 < h) (hhn : h < n) (hg : 0 < gamma)
    (hT : n/h ≤ T) (hband : |gamma-T| ≤ 1) :
    1 ≤ (T+1)/gamma ∧ (T+1)/gamma ≤ (n+h)/(n-h) ∧
      (T+1)/gamma-1 ≤ 2/gamma := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hband
  have hTh := (div_le_iff₀ hh).mp hT
  refine ⟨(le_div_iff₀ hg).mpr (by linarith), ?_, ?_⟩
  · apply (div_le_div_iff₀ hg (by linarith : 0 < n-h)).mpr
    nlinarith [mul_nonneg (show 0 ≤ gamma-(T-1) by linarith)
      (show 0 ≤ n+h by linarith)]
  · have hid : (T+1)/gamma-1=(T+1-gamma)/gamma := by field_simp
    rw [hid]
    exact (div_le_div_iff_of_pos_right hg).mpr (by linarith)









/-- The explicit endpoint estimate leaves strict room after two modulus steps. -/
theorem class_spacing_bound {n h : ℝ} (hh : 0 ≤ h) (hhn : h < n) :
    (n-2*h-1)*((n+h)/(n-h)) < n+1 := by
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < n-h)).mpr
  nlinarith [sq_nonneg h]

/-- A class representative selected by spacing survives the first fast exit. -/
theorem class_flank_survives {n h b z full : ℝ}
    (hh : 0 < h) (hhn : h < n) (hz : 0 ≤ z)
    (hb : b ≤ n-2*h-1) (hbound : 0 ≤ n-2*h-1)
    (hzmax : z ≤ (n+h)/(n-h)) (hfull : n+1 ≤ full) :
    b*z < full := by
  calc
    b*z ≤ (n-2*h-1)*z := mul_le_mul_of_nonneg_right hb hz
    _ ≤ (n-2*h-1)*((n+h)/(n-h)) := mul_le_mul_of_nonneg_left hzmax hbound
    _ < n+1 := class_spacing_bound hh.le hhn
    _ ≤ full := hfull





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









/-- Normalize the speed and determinant window without any extra certificate. -/
theorem active_window {n r m q : ℕ} (F : ActiveFibre n r m q) (hm : 0 < m) :
    (q:ℝ)/((m:ℝ)*r)=(F.U:ℝ)/((F.h:ℝ)*m) ∧
    |(q:ℝ)/((m:ℝ)*r)-(n:ℝ)*F.V/F.h| ≤ 1 := by
  have hh : (0:ℝ) < F.h := by exact_mod_cast (show 0 < F.h by have := F.h_two; omega)
  have hd : (0:ℝ) < F.d := by exact_mod_cast F.d_pos
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hrEq : (r:ℝ)=(F.d:ℝ)*F.h := by exact_mod_cast F.r_eq
  have hqEq : (q:ℝ)=(F.d:ℝ)*F.U := by exact_mod_cast F.q_eq
  have heq : (q:ℝ)/((m:ℝ)*r)=(F.U:ℝ)/((F.h:ℝ)*m) := by
    rw [hrEq,hqEq]; field_simp
  refine ⟨heq,?_⟩
  rw [heq]
  have hw : |(n:ℝ)*m*F.V-F.U| ≤ (F.h:ℝ)*m := by exact_mod_cast F.window
  have hid : (F.U:ℝ)/((F.h:ℝ)*m)-(n:ℝ)*F.V/F.h=
      -((n:ℝ)*m*F.V-F.U)/((F.h:ℝ)*m) := by field_simp; ring
  rw [hid,abs_div,abs_neg,abs_of_pos (mul_pos hh hmR)]
  exact (div_le_one (mul_pos hh hmR)).mpr hw







end LonelyRunner.SmallFibrePhase

namespace LonelyRunner.PrimitiveFibre
open CollectiveUnits CollectiveFibreNormalForm

theorem linear_congruence_iff {h V U : ℕ} {b c : ℤ}
    (hbc : (h:ℤ) ∣ b-c) :
    (h:ℤ) ∣ (V:ℤ)*b-U ↔ (h:ℤ) ∣ (V:ℤ)*c-U := by
  have hd := dvd_mul_of_dvd_right hbc (V:ℤ)
  constructor
  · intro hb
    have heq : ((V:ℤ)*b-U)-(V:ℤ)*(b-c)=(V:ℤ)*c-U := by ring
    simpa only [heq] using dvd_sub hb hd
  · intro hc
    have heq : ((V:ℤ)*c-U)+(V:ℤ)*(b-c)=(V:ℤ)*b-U := by ring
    simpa only [heq] using dvd_add hc hd

theorem linear_mod_iff {h r V U b : ℕ} (hd : h ∣ r) :
    (h:ℤ) ∣ (V:ℤ)*b-U ↔ (h:ℤ) ∣ (V:ℤ)*(b%r:ℕ)-U := by
  apply linear_congruence_iff
  exact dvd_trans (by exact_mod_cast hd)
    (Nat.modEq_iff_dvd.mp (Nat.mod_mod b r))



@[simp] theorem mem_fibre {n r h V U b : ℕ} :
    b ∈ fibre n r h V U ↔ b ∈ primitiveFlanks n r ∧ (h:ℤ) ∣ (V:ℤ)*b-U := by
  simp [fibre]

theorem card_fibre {n r h V U : ℕ} (hr : 0 < r) (hrn : r < n)
    (hlarge : n ≤ 2*r) (hh : 0 < h) (hd : h ∣ r)
    (hU : Nat.Coprime h U) (hV : Nat.Coprime h V) :
    (fibre n r h V U).card*h.totient=r.totient := by
  classical
  have heq : (fibre n r h V U).card =
      ((units r).filter (fun b : ℕ => (h:ℤ) ∣ (V:ℤ)*b-U)).card := by
    apply Finset.card_bij (fun b _ => b%r)
    · intro b hb
      obtain ⟨hbf,hbc⟩ := mem_fibre.mp hb
      have hcop := (mem_primitiveFlanks.mp hbf).2.2
      apply Finset.mem_filter.mpr
      refine ⟨mem_units.mpr ⟨Nat.mod_lt _ hr,?_⟩,(linear_mod_iff hd).mp hbc⟩
      change Nat.gcd r (b%r)=1
      rw [Nat.gcd_comm,← Nat.gcd_rec]
      exact hcop
    · intro b hb c hc heq
      exact primitiveFlanks_mod_injective (mem_fibre.mp hb).1 (mem_fibre.mp hc).1 heq
    · intro c hc
      obtain ⟨hcu,hcmod⟩ := Finset.mem_filter.mp hc
      obtain ⟨b,hb,hbn,hcop,hmod⟩ := lift_unit hlarge hrn hcu
      refine ⟨b,mem_fibre.mpr ⟨mem_primitiveFlanks.mpr ⟨hb,hbn,hcop⟩,?_⟩,hmod⟩
      exact (linear_mod_iff hd).mpr (by simpa only [hmod] using hcmod)
  rw [heq]
  exact CollectiveFibreCounting.congruence_fibre_card hr hh hd hU hV

theorem same_residue {h V U b c : ℕ} (hV : Nat.Coprime h V)
    (hb : (h:ℤ) ∣ (V:ℤ)*b-U) (hc : (h:ℤ) ∣ (V:ℤ)*c-U) : b%h=c%h := by
  have hmul : (h:ℤ) ∣ (V:ℤ)*((c:ℤ)-b) := by
    have heq : ((V:ℤ)*c-U)-((V:ℤ)*b-U)=(V:ℤ)*((c:ℤ)-b) := by ring
    simpa only [heq] using dvd_sub hc hb
  exact Nat.modEq_iff_dvd.mpr (hV.isCoprime.dvd_of_dvd_mul_left hmul)

/-- Three members of one residue class include one at least two modulus
steps below the terminal endpoint. -/
theorem exists_low {n h : ℕ} (S : Finset ℕ) (hcard : 3 ≤ S.card)
    (hn : ∀b ∈ S, b < n) (hmod : ∀b ∈ S, ∀c ∈ S, b%h=c%h) :
    ∃b ∈ S, b+2*h+1 ≤ n := by
  obtain ⟨b,c,d,hb,hc,hd,hbc,hbd,hcd⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  have hgap (a e : ℕ) (ha : a ∈ S) (he : e ∈ S) (hne : a≠e) :
      a+h ≤ e ∨ e+h ≤ a := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hdiv := (Nat.modEq_iff_dvd' hlt.le).mp (hmod a ha e he)
      have hh := Nat.le_of_dvd (show 0 < e-a by omega) hdiv
      exact Or.inl (by omega)
    · have hdiv := (Nat.modEq_iff_dvd' hlt.le).mp (hmod e he a ha)
      have hh := Nat.le_of_dvd (show 0 < a-e by omega) hdiv
      exact Or.inr (by omega)
  have hg₁ := hgap b c hb hc hbc
  have hg₂ := hgap b d hb hd hbd
  have hg₃ := hgap c d hc hd hcd
  have hbn := hn b hb
  have hcn := hn c hc
  have hdn := hn d hd
  by_contra! hno
  have hh₁ := hno b hb
  have hh₂ := hno c hc
  have hh₃ := hno d hd
  omega

/-- A half-sized small quotient fibre supplies the flank needed by the
geometric exit bound once the ambient unit group has at least six elements. -/
theorem active_low {n r m q : ℕ} (F : ActiveFibre n r m q)
    (hr : 0 < r) (hrn : r < n) (hlarge : n ≤ 2*r)
    (hsmall : F.h=3 ∨ F.h=4 ∨ F.h=6) (hphi : 6 ≤ r.totient) :
    ∃b ∈ primitiveFlanks n r, (F.h:ℤ) ∣ (F.V:ℤ)*b-F.U ∧ b+2*F.h+1 ≤ n := by
  have hh : 0 < F.h := by have := F.h_two; omega
  have hd : F.h ∣ r := ⟨F.d,by nlinarith only [F.r_eq]⟩
  have hcard := card_fibre hr hrn hlarge hh hd F.copU F.copV
  have ht : F.h.totient=2 := by rcases hsmall with ht | ht | ht <;> rw [ht] <;> decide
  rw [ht] at hcard
  obtain ⟨b,hb,hbs⟩ := exists_low (fibre n r F.h F.V F.U) (by omega)
    (fun b hb => (mem_primitiveFlanks.mp (mem_fibre.mp hb).1).2.1)
    (fun b hb c hc => same_residue F.copV (mem_fibre.mp hb).2 (mem_fibre.mp hc).2)
  exact ⟨b,(mem_fibre.mp hb).1,(mem_fibre.mp hb).2,hbs⟩

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



/-- The active fastest band exits at the bounded clock supplied by its
normal form. -/
theorem exit_bounds {n r m u : ℕ} (G : ActiveFibre n r m u)
    (hm : 0 < m) (hn : 0 < n) (hgn : G.h < n) (hu : 0 < u) :
    let gamma : ℝ := (u:ℝ)/((m:ℝ)*r)
    let T : ℝ := (n:ℝ)*G.V/G.h
    1 ≤ (T+1)/gamma ∧ (T+1)/gamma ≤ ((n:ℝ)+G.h)/((n:ℝ)-G.h) ∧
      (T+1)/gamma-1 ≤ 2/gamma := by
  dsimp
  have hh : (0:ℝ) < G.h := by exact_mod_cast (show 0 < G.h by have := G.h_two; omega)
  have hr : (0:ℝ) < r := by
    have hd := G.d_pos
    have ht := G.h_two
    have hEq := G.r_eq
    exact_mod_cast (show 0 < r by nlinarith)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  apply TwoBlockerGeometry.active_band_exit_bound hh (by exact_mod_cast hgn)
    (div_pos (by exact_mod_cast hu) (by positivity))
  · apply (div_le_div_iff_of_pos_right hh).mpr
    have hV : (1:ℝ) ≤ G.V := by exact_mod_cast G.v_pos
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    nlinarith
  · exact (SmallFibrePhase.active_window G hm).2





end LonelyRunner.ComplementaryEscape

namespace LonelyRunner.SmallFibreTable
open CollectiveUnits CollectiveFibreNormalForm



/-- Sharedness supplies the only extra multiplier bound needed beyond the
strict full-period margin, namely (r,n)=(12,14). -/
theorem minimum_le {n r s m k : ℕ} (hrn : r < n) (hm : 0 < m)
    (hrs : r < s) (hsn : s < n) (hshared : m*r=k*s) (hfull : n < m*(n-r)) :
    minimumMultiplier r n ≤ m := by
  unfold minimumMultiplier
  split_ifs with he
  · obtain ⟨rfl,rfl⟩ := he
    have hs : s=13 := by omega
    subst s
    by_contra! hh
    interval_cases m <;> omega
  · have hh : n/(n-r) < m := (Nat.div_lt_iff_lt_mul (by omega : 0 < n-r)).mpr hfull
    omega





set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_eight : ∀n : Fin 25, ∀h C : Fin 7,
    10 ≤ n.val → n.val ≤ 16 → (h.val=3 ∨ h.val=4 ∨ h.val=6) → h.val ∣ 8 →
    C.val<h.val → Nat.Coprime h.val C.val → ∃b : Fin 25, Entry 8 n.val h.val C.val b.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_twelve : ∀n : Fin 25, ∀h C : Fin 7,
    14 ≤ n.val → n.val ≤ 24 → (h.val=3 ∨ h.val=4 ∨ h.val=6) → h.val ∣ 12 →
    C.val<h.val → Nat.Coprime h.val C.val → ∃b : Fin 25, Entry 12 n.val h.val C.val b.val := by
  decide

theorem table {n r h C : ℕ} (hr : r=8 ∨ r=12) (hnr : r+2 ≤ n) (hn : n ≤ 2*r)
    (hh : h=3 ∨ h=4 ∨ h=6) (hd : h ∣ r) (hC : C<h) (hc : Nat.Coprime h C) :
    ∃b : ℕ, Entry r n h C b := by
  have hh25 : h < 7 := by rcases hh with rfl | rfl | rfl <;> decide
  have hC25 : C < 7 := hC.trans hh25
  rcases hr with rfl | rfl
  · obtain ⟨b,hb⟩ := table_eight ⟨n,by omega⟩ ⟨h,hh25⟩ ⟨C,hC25⟩ hnr hn hh hd hC hc
    exact ⟨b,hb⟩
  · obtain ⟨b,hb⟩ := table_twelve ⟨n,by omega⟩ ⟨h,hh25⟩ ⟨C,hC25⟩ hnr hn hh hd hC hc
    exact ⟨b,hb⟩

/-- The two coarse-table exceptions are resolved for every multiplier and
active determinant, using the actual congruence. -/
theorem exception_nineteen {m V U : ℕ} (hm : 3 ≤ m) (hV : 0 < V)
    (hwin : |(19:ℤ)*m*V-U| ≤ (6:ℤ)*m)
    (hcong : (6:ℤ) ∣ (V:ℤ)*11-U) : (11:ℝ)*(19*V+6) < 7*U := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hVR : (1:ℝ) ≤ V := by exact_mod_cast hV
  have hw : |(19:ℝ)*m*V-U| ≤ (6:ℝ)*m := by exact_mod_cast hwin
  have hl : (m:ℝ)*(19*V-6) ≤ U := by linarith [(abs_le.mp hw).2]
  by_cases hm3 : m=3
  · subst m
    by_cases hV1 : V=1
    · subst V
      have hwZ := (abs_le.mp hwin).2
      norm_num only [Nat.cast_ofNat, mul_one] at hwZ hcong
      have hU : 41 ≤ U := by omega
      have hUR : (41:ℝ) ≤ U := by exact_mod_cast hU
      norm_num only [Nat.cast_one]
      linarith only [hUR]
    · have hV2 : (2:ℝ) ≤ V := by exact_mod_cast (show 2 ≤ V by omega)
      norm_num at hl
      nlinarith only [hl,hV2]
  · have hm4 : (4:ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    have hh := mul_le_mul_of_nonneg_right hm4 (show 0 ≤ 19*(V:ℝ)-6 by linarith)
    nlinarith only [hl,hh,hVR]

theorem exception_twenty {m V U : ℕ} (hm : 3 ≤ m) (hV : 0 < V)
    (hwin : |(20:ℤ)*m*V-U| ≤ (6:ℤ)*m)
    (hcong : (6:ℤ) ∣ (V:ℤ)*13-U) : (13:ℝ)*(20*V+6) < 8*U := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hVR : (1:ℝ) ≤ V := by exact_mod_cast hV
  have hw : |(20:ℝ)*m*V-U| ≤ (6:ℝ)*m := by exact_mod_cast hwin
  have hl : (m:ℝ)*(20*V-6) ≤ U := by linarith [(abs_le.mp hw).2]
  by_cases hm3 : m=3
  · subst m
    by_cases hV1 : V=1
    · subst V
      have hwZ := (abs_le.mp hwin).2
      norm_num only [Nat.cast_ofNat, mul_one] at hwZ hcong
      have hU : 43 ≤ U := by omega
      have hUR : (43:ℝ) ≤ U := by exact_mod_cast hU
      norm_num only [Nat.cast_one]
      linarith only [hUR]
    · have hV2 : (2:ℝ) ≤ V := by exact_mod_cast (show 2 ≤ V by omega)
      norm_num at hl
      nlinarith only [hl,hV2]
  · have hm4 : (4:ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    have hh := mul_le_mul_of_nonneg_right hm4 (show 0 ≤ 20*(V:ℝ)-6 by linarith)
    nlinarith only [hl,hh,hVR]

theorem margin_of_integer {n r m u b : ℕ} (G : ActiveFibre n r m u)
    (hm : 0 < m) (hu : 0 < u)
    (hb : (b:ℝ)*((n:ℝ)*G.V+G.h) < ((n:ℝ)-r)*G.U) :
    (b:ℝ)*(((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))) < (m:ℝ)*((n:ℝ)-r) := by
  have hh : (0:ℝ) < G.h := by exact_mod_cast (show 0 < G.h by have := G.h_two; omega)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hU : (0:ℝ) < G.U := by
    exact_mod_cast (show 0 < G.U by have := G.q_eq; nlinarith)
  have heq : ((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))=
      (m:ℝ)*((n:ℝ)*G.V+G.h)/G.U := by
    rw [(SmallFibrePhase.active_window G hm).1]
    field_simp
  rw [heq,← mul_div_assoc]
  apply (div_lt_iff₀ hU).mpr
  nlinarith only [mul_lt_mul_of_pos_left hb hmR]

theorem margin_of_entry {n r m u b C : ℕ} (G : ActiveFibre n r m u)
    (hrn : r < n) (hm : 0 < m) (hu : 0 < u) (hgn : G.h < n)
    (hM : minimumMultiplier r n ≤ m)
    (hb : Entry r n G.h C b) (hcong : (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U) :
    (b:ℝ)*(((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))) < (m:ℝ)*((n:ℝ)-r) := by
  obtain ⟨_,_,_,_,hcases⟩ := hb
  rcases hcases with hcoarse | hex | hex
  · have hbound := (ComplementaryEscape.exit_bounds G hm (by omega) hgn hu).2.1
    have hbn : (b:ℝ)*((n:ℝ)+G.h) <
        (minimumMultiplier r n:ℝ)*((n:ℝ)-r)*((n:ℝ)-G.h) := by
      have ht : (b:ℝ)*(n+G.h) < (minimumMultiplier r n:ℝ)*(n-r:ℕ)*(n-G.h:ℕ) := by
        exact_mod_cast hcoarse
      simpa only [Nat.cast_sub hrn.le,Nat.cast_sub hgn.le] using ht
    have hden : (0:ℝ) < (n:ℝ)-G.h := sub_pos.mpr (by exact_mod_cast hgn)
    have hcoarseR : (b:ℝ)*(((n:ℝ)+G.h)/((n:ℝ)-G.h)) <
        (minimumMultiplier r n:ℝ)*((n:ℝ)-r) := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hden).mpr hbn
    have hmR : (minimumMultiplier r n:ℝ) ≤ m := by exact_mod_cast hM
    exact (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg b)).trans_lt
      (hcoarseR.trans_le (mul_le_mul_of_nonneg_right hmR (sub_nonneg.mpr (by exact_mod_cast hrn.le))))
  · obtain ⟨rfl,rfl,hh,_,rfl⟩ := hex
    apply margin_of_integer G hm hu
    have hm3 : 3 ≤ m := by simpa [minimumMultiplier] using hM
    have ht := exception_nineteen hm3 G.v_pos
      (by simpa only [hh,Nat.cast_ofNat] using G.window)
      (by simpa only [hh,Nat.cast_ofNat] using hcong)
    simpa only [hh,Nat.cast_ofNat,show (19:ℝ)-12=7 by norm_num] using ht
  · obtain ⟨rfl,rfl,hh,_,rfl⟩ := hex
    apply margin_of_integer G hm hu
    have hm3 : 3 ≤ m := by simpa [minimumMultiplier] using hM
    have ht := exception_twenty hm3 G.v_pos
      (by simpa only [hh,Nat.cast_ofNat] using G.window)
      (by simpa only [hh,Nat.cast_ofNat] using hcong)
    simpa only [hh,Nat.cast_ofNat,show (20:ℝ)-12=8 by norm_num] using ht

/-- Every active small fibre over the two low-totient moduli has a surviving
primitive representative, without bounding its speed or determinant. -/
theorem exists_surviving {n r s m k u : ℕ} (G : ActiveFibre n r m u)
    (hr : r=8 ∨ r=12) (hrs : r < s) (hsn : s < n) (hlarge : n ≤ 2*r)
    (hm : 0 < m) (hu : 0 < u) (hshared : m*r=k*s) (hfull : n < m*(n-r))
    (hsmall : G.h=3 ∨ G.h=4 ∨ G.h=6) :
    ∃b ∈ primitiveFlanks n r, (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U ∧
      (b:ℝ)*(((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))) < (m:ℝ)*((n:ℝ)-r) := by
  classical
  have hr0 : 0 < r := by rcases hr with rfl | rfl <;> decide
  have hrn : r < n := hrs.trans hsn
  have hh0 : 0 < G.h := by have := G.h_two; omega
  have hhd : G.h ∣ r := ⟨G.d,by nlinarith only [G.r_eq]⟩
  have hgn : G.h < n := by
    have hr8 : 8 ≤ r := by rcases hr with rfl | rfl <;> decide
    rcases hsmall with ht | ht | ht <;> omega
  have hc := PrimitiveFibre.card_fibre (n:=n) hr0 hrn hlarge hh0 hhd G.copU G.copV
  have hphi := Nat.totient_pos.mpr hr0
  have hcard : 0 < (PrimitiveFibre.fibre n r G.h G.V G.U).card := by nlinarith
  obtain ⟨b₀,hb₀⟩ := Finset.card_pos.mp hcard
  obtain ⟨hb₀,hb₀cong⟩ := PrimitiveFibre.mem_fibre.mp hb₀
  let C := b₀%G.h
  have hC : C < G.h := Nat.mod_lt _ hh0
  have hCcop : Nat.Coprime G.h C := by
    change Nat.gcd G.h (b₀%G.h)=1
    rw [Nat.gcd_comm,← Nat.gcd_rec]
    exact ((mem_primitiveFlanks.mp hb₀).2.2.of_dvd_left hhd)
  obtain ⟨b,hb⟩ := table hr (by omega) hlarge hsmall hhd hC hCcop
  have hcong : (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U := by
    have heq : b%G.h=b₀%G.h := hb.2.2.2.1
    exact (PrimitiveFibre.linear_congruence_iff
      (Nat.modEq_iff_dvd.mp heq.symm)).mpr hb₀cong
  refine ⟨b,mem_primitiveFlanks.mpr ⟨hb.1,hb.2.1,hb.2.2.1⟩,hcong,?_⟩
  exact margin_of_entry G hrn hm hu hgn (minimum_le hrn hm hrs hsn hshared hfull) hb hcong

end LonelyRunner.SmallFibreTable

namespace LonelyRunner.SharedSlowestSmall
open CollectiveSecondFastest



/-- At n=11,r=9, sharedness forces m>=10. A low primitive flank survives the
phase-uniform escape even if the two bands hand coverage to one another. -/
theorem strict_eleven {m k q u : ℕ} {R : Finset ℕ}
    (hm : 0 < m) (hshared : m*9=k*10) (hrR : 9 ∈ R)
    (hpq : m*9 < q) (hqu : q < u) :
    SeparatedMulti.HasStrictTime 11 R {m*9,q,u} := by
  have hm10 : 10 ≤ m := by
    by_contra! hh
    interval_cases m <;> omega
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  let slow : ℝ := (q:ℝ)/((m:ℝ)*9)
  let fast : ℝ := (u:ℝ)/((m:ℝ)*9)
  let a := numerator 9 2
  have hs : 1 < slow := by
    apply (lt_div_iff₀ (by positivity : (0:ℝ) < m*9)).mpr
    simpa using (show (m:ℝ)*9 < q by exact_mod_cast hpq)
  have horder : slow < fast := div_lt_div_of_pos_right (by exact_mod_cast hqu) (by positivity)
  obtain ⟨z,hz,hqz,huz⟩ := strict_before_eight (n:=11)
    (theta:=(q:ℝ)*a/9) (phi:=(u:ℝ)*a/9) (by norm_num) hs horder
  apply SharedSlowestHalf.strict_of_clock (r:=9) (b:=2)
    (by decide) (by decide) hm hrR (by decide) (by decide) hz.1
    (by norm_num; linarith [hz.2])
  · have hm10R : (10:ℝ) ≤ m := by exact_mod_cast hm10
    norm_num
    linarith [hz.2]
  · have he : (q:ℝ)*((a:ℝ)/9-z/((11:ℝ)*m*9))=(q:ℝ)*a/9-slow*z/11 := by
      dsimp [slow]; field_simp
    change 1/(11:ℝ) < ndist ((q:ℝ)*((a:ℝ)/9-z/((11:ℝ)*m*9)))
    rw [he]
    exact hqz
  · have he : (u:ℝ)*((a:ℝ)/9-z/((11:ℝ)*m*9))=(u:ℝ)*a/9-fast*z/11 := by
      dsimp [fast]; field_simp
    change 1/(11:ℝ) < ndist ((u:ℝ)*((a:ℝ)/9-z/((11:ℝ)*m*9)))
    rw [he]
    exact huz

end LonelyRunner.SharedSlowestSmall

namespace LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm





end LonelyRunner.SharedSlowest

namespace LonelyRunner.UniqueSharedRepair







end LonelyRunner.UniqueSharedRepair

open LonelyRunner
open LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- The two complementary small-fibre branches have a full strict-time proof,
including the low-totient table and the possible small-baseline handoff. -/
theorem solution {n r s m k q u : ℕ} {R : Finset ℕ}
    (F : ActiveFibre n r m q) (G : ActiveFibre n r m u)
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 0 < m) (hk : 0 < k) (hshared : m*r=k*s)
    (hpq : m*r < q) (hqu : q < u)
    (hF : F.h=3 ∨ F.h=4 ∨ F.h=6) (hG : G.h=3 ∨ G.h=4 ∨ G.h=6)
    (hcomp : ∀c ∈ units r, CollectiveBoundary.Blocks (n:ℤ) r m u c →
      ¬CollectiveBoundary.Blocks (n:ℤ) r m q c) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  have hr0 : 0 < r := by omega
  have hrn : r < n := hrs.trans hsn
  have hrmax : r+2 ≤ n := by omega
  have hfull := SharedMiddleArithmetic.shared_full_period hr0 hrs hsn hk hshared
  by_cases hsmall : r=9 ∧ n=11
  · obtain ⟨rfl,rfl⟩ := hsmall
    have hs : s=10 := by omega
    subst s
    exact SharedSlowestSmall.strict_eleven hm hshared hrR hpq hqu
  have hsize : 12 ≤ n ∨ F.h=4 := by
    by_contra! hh
    have hd : F.h ∣ r := ⟨F.d,by nlinarith only [F.r_eq]⟩
    rcases hF with h3 | h4 | h6
    · rw [h3] at hd
      omega
    · exact hh.2 h4
    · rw [h6] at hd
      omega
  have hgn : G.h < n := by rcases hG with ht | ht | ht <;> omega
  have hhR : (0:ℝ) < G.h := by exact_mod_cast (show 0 < G.h by have := G.h_two; omega)
  have hgnR : (G.h:ℝ) < n := by exact_mod_cast hgn
  have hu : 0 < u := by omega
  by_cases hphi : 6 ≤ r.totient
  · obtain ⟨b,hb,hbg,hbsmall⟩ := PrimitiveFibre.active_low G hr0 hrn hlarge hG hphi
    apply ComplementaryEscape.strict_of_surviving_fibre F G hr hrmax hm hrR hlarge
      hpq hqu hF hG hsize hcomp hb hbg
    have hbR : (b:ℝ)+2*G.h+1 ≤ n := by exact_mod_cast hbsmall
    have hz := ComplementaryEscape.exit_bounds G hm (by omega) hgn hu
    apply TwoBlockerGeometry.class_flank_survives hhR hgnR (by linarith [hz.1])
      (by linarith) (by have : (0:ℝ) ≤ b := Nat.cast_nonneg b; linarith) hz.2.1
    have ht : (n:ℝ)+1 ≤ (m:ℝ)*(n-r:ℕ) := by
      exact_mod_cast (show n+1 ≤ m*(n-r) by omega)
    simpa only [Nat.cast_sub hrn.le] using ht
  · have hlow : r=8 ∨ r=12 := by
      rcases SmallTotient.eq_eight_ten_twelve hr (by omega) with h8 | h10 | h12
      · exact Or.inl h8
      · have hd : G.h ∣ r := ⟨G.d,by nlinarith only [G.r_eq]⟩
        rcases hG with ht | ht | ht <;> norm_num [ht,h10] at hd
      · exact Or.inr h12
    obtain ⟨b,hb,hbg,hmargin⟩ := SmallFibreTable.exists_surviving G hlow hrs hsn
      hlarge hm hu hshared hfull hG
    exact ComplementaryEscape.strict_of_surviving_fibre F G hr hrmax hm hrR hlarge
      hpq hqu hF hG hsize hcomp hb hbg hmargin
