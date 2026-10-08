-- Prove2me | solution 1 for LonelyRunner.ComplementaryEscape.strict_of_surviving_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:13:24.420127+00:00
-- url     : https://prove2.me/submissions/065ab347-9201-4e5d-86b0-628cefc7c1f1

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
import Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm







/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m

@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]



@[simp] theorem ndist_neg (x : ℝ) : ndist (-x) = ndist x := by
  rw [ndist_eq_norm, ndist_eq_norm, AddCircle.coe_neg, norm_neg]











/-- `δ ≤ ‖x‖` iff `x` is at distance at least `δ` from every integer. -/
theorem le_ndist_iff {δ x : ℝ} : δ ≤ ndist x ↔ ∀ m : ℤ, δ ≤ |x - m| :=
  ⟨fun h m => h.trans (ndist_le_abs_sub x m), fun h => h (round x)⟩















end LonelyRunner

namespace LonelyRunner.BadCover

theorem continuous_ndist : Continuous ndist := by
  have heq : ndist = fun x : ℝ => ‖(x : UnitAddCircle)‖ := funext ndist_eq_norm
  rw [heq]
  exact continuous_norm.comp (AddCircle.continuous_mk' (1 : ℝ))



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

/-- `ndist` is 1-Lipschitz. -/
theorem ndist_le_add (x y : ℝ) : ndist x ≤ |x - y| + ndist y := by
  calc ndist x ≤ |x - round y| := ndist_le_abs_sub x (round y)
    _ = |(x - y) + (y - round y)| := by ring_nf
    _ ≤ |x - y| + |y - round y| := abs_add_le _ _
    _ = |x - y| + ndist y := rfl



/-- If `m ∤ v` then `‖v/m‖ ≥ 1/m`. -/
theorem one_div_le_ndist_div {m : ℕ} (hm : 0 < m) {v : ℤ} (hv : ¬ (m : ℤ) ∣ v) :
    1 / (m : ℝ) ≤ ndist ((v : ℝ) / m) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_ndist_iff]
  intro n
  have hne : v - n * m ≠ 0 := by
    intro h
    exact hv ⟨n, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((v - n * m : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |v - n * m| := Int.one_le_abs hne
    exact_mod_cast this
  have h2 : ((v : ℝ) / m - n) = ((v - n * m : ℤ) : ℝ) / m := by
    push_cast; field_simp
  rw [h2, abs_div, abs_of_pos hmr, div_le_div_iff_of_pos_right hmr]
  exact h1











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



@[simp] theorem mem_units {r u : ℕ} : u ∈ units r ↔ u < r ∧ Nat.Coprime r u := by
  simp [units]

















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

/-- During a faster band of remaining length at most `2 / fast`, a slower
runner initially separated by `kappa - 1/n` stays strictly safe if `n*kappa≥4`.
Strict speed ordering preserves strictness at the threshold `n*kappa=4`. -/
theorem no_handoff {n slow fast z theta kappa : ℝ}
    (hn : 0 < n) (hslow : 0 < slow) (horder : slow < fast)
    (hz : 1 ≤ z) (hstep : z-1 ≤ 2/fast)
    (hgap : kappa-1/n ≤ ndist (theta-slow/n))
    (hcapacity : 4 ≤ n*kappa) :
    1/n < ndist (theta-slow*z/n) := by
  have hfast : 0 < fast := lt_trans hslow horder
  have hshift : slow*(z-1) < 2 := by
    calc
      _ ≤ slow*(2/fast) := mul_le_mul_of_nonneg_left hstep hslow.le
      _ = (2*slow)/fast := by ring
      _ < 2 := (div_lt_iff₀ hfast).mpr (by linarith)
  have hshift0 : 0 ≤ slow*(z-1)/n := div_nonneg (mul_nonneg hslow.le (by linarith)) hn.le
  have hshiftbound : slow*(z-1)/n < 2/n := div_lt_div_of_pos_right hshift hn
  have heq : (theta-slow/n)-(theta-slow*z/n)=slow*(z-1)/n := by ring
  have htri := ndist_le_add (theta-slow/n) (theta-slow*z/n)
  rw [heq,abs_of_nonneg hshift0] at htri
  have hk : 4/n ≤ kappa := (div_le_iff₀ hn).mpr (by nlinarith)
  have hfour : 4/n=4*(1/n) := by ring
  have htwo : 2/n=2*(1/n) := by ring
  rw [hfour] at hk
  rw [htwo] at hshiftbound
  linarith

/-- Opposite quotient-three or quotient-six phases have gap one third. -/
theorem no_handoff_thirds {n slow fast z theta : ℝ}
    (hn : 12 ≤ n) (hslow : 0 < slow) (horder : slow < fast)
    (hz : 1 ≤ z) (hstep : z-1 ≤ 2/fast)
    (hgap : 1/3-1/n ≤ ndist (theta-slow/n)) :
    1/n < ndist (theta-slow*z/n) :=
  no_handoff (by linarith) hslow horder hz hstep hgap (by linarith)

/-- Opposite quotient-four phases have gap one half. -/
theorem no_handoff_halves {n slow fast z theta : ℝ}
    (hn : 8 ≤ n) (hslow : 0 < slow) (horder : slow < fast)
    (hz : 1 ≤ z) (hstep : z-1 ≤ 2/fast)
    (hgap : 1/2-1/n ≤ ndist (theta-slow/n)) :
    1/n < ndist (theta-slow*z/n) :=
  no_handoff (by linarith) hslow horder hz hstep hgap (by linarith)











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

theorem congruence_iff_mod {h V b U : ℕ} :
    (h:ℤ) ∣ (V:ℤ)*b-U ↔ (V*b)%h=U%h := by
  have hh := (Nat.modEq_iff_dvd (n:=h) (a:=U) (b:=V*b)).symm
  push_cast at hh
  exact hh.trans eq_comm

theorem unit_sign {h v : ℕ} (hh : h=3 ∨ h=4 ∨ h=6) (hv : Nat.Coprime h v) :
    v%h=1 ∨ v%h+1=h := by
  have hpos : 0 < h := by rcases hh with rfl | rfl | rfl <;> decide
  have hlt : h < 7 := by rcases hh with rfl | rfl | rfl <;> decide
  have hvlt := Nat.mod_lt v hpos
  have hc : Nat.Coprime h (v%h) := by
    change Nat.gcd h (v%h)=1
    rw [Nat.gcd_comm,← Nat.gcd_rec]
    exact hv
  have hfinite : ∀a c : Fin 7, (a.val=3 ∨ a.val=4 ∨ a.val=6) →
      c.val<a.val → Nat.Coprime a.val c.val → c.val=1 ∨ c.val+1=a.val := by decide
  exact hfinite ⟨h,hlt⟩ ⟨v%h,hvlt.trans hlt⟩ hh hvlt hc

/-- On a two-element unit group, a unit outside a prescribed fibre lies in
the opposite fibre. -/
theorem opposite_congruence {h V U b : ℕ} (hh : h=3 ∨ h=4 ∨ h=6)
    (hV : Nat.Coprime h V) (hU : Nat.Coprime h U) (hb : Nat.Coprime h b)
    (hnot : ¬(h:ℤ) ∣ (V:ℤ)*b-U) : (h:ℤ) ∣ (V:ℤ)*b+U := by
  have hs₁ := unit_sign hh (hV.mul_right hb)
  have hs₂ := unit_sign hh hU
  have hne : (V*b)%h ≠ U%h := fun he => hnot (congruence_iff_mod.mpr he)
  have heq : (V*b)%h+U%h=h := by omega
  have hd : h ∣ V*b+U := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod,heq,Nat.mod_self])
  exact_mod_cast hd

/-- The arithmetic fibre determines a literal phase up to an integer. -/
theorem phase_lap {n r m q b : ℕ} {a c V : ℤ}
    (F : ActiveFibre n r m q) (hu : a*(b:ℤ)-c*r=1)
    (hcong : (F.h:ℤ) ∣ V*b-F.U) :
    ∃J : ℤ, (q:ℝ)*(a:ℝ)/r=(J:ℝ)+(V:ℝ)/F.h := by
  have hhpos : (0:ℝ) < F.h := by exact_mod_cast (show 0 < F.h by have := F.h_two; omega)
  have hdpos : (0:ℝ) < F.d := by exact_mod_cast F.d_pos
  have hrEq : (r:ℝ)=(F.d:ℝ)*F.h := by exact_mod_cast F.r_eq
  have hqEq : (q:ℝ)=(F.d:ℝ)*F.U := by exact_mod_cast F.q_eq
  have hrEqZ : (r:ℤ)=(F.d:ℤ)*F.h := by exact_mod_cast F.r_eq
  obtain ⟨k,hk⟩ := hcong
  have hd : (F.h:ℤ) ∣ (F.U:ℤ)*a-V := by
    refine ⟨V*c*F.d-k*a,?_⟩
    linear_combination V*hu - a*hk + V*c*hrEqZ
  obtain ⟨J,hJ⟩ := hd
  refine ⟨J,?_⟩
  have hJR : (F.U:ℝ)*a-V=(F.h:ℝ)*J := by exact_mod_cast hJ
  have heq : (q:ℝ)*(a:ℝ)/r=(F.U:ℝ)*a/F.h := by
    calc
      _ = ((F.d:ℝ)*F.U)*a/((F.d:ℝ)*F.h) := by rw [hrEq,hqEq]
      _ = _ := by field_simp
  rw [heq]
  apply (div_eq_iff (ne_of_gt hhpos)).mpr
  have hdiv : (V:ℝ)/F.h*F.h=V := by field_simp
  nlinarith only [hJR,hdiv]

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

private theorem not_dvd_of_coprime {h v : ℕ} (hh : 2 ≤ h)
    (hv : Nat.Coprime h v) : ¬ (h:ℤ) ∣ (v:ℤ) := by
  intro hd
  have hdN : h ∣ v := by exact_mod_cast hd
  have hh1 : h ∣ 1 := by
    rw [← hv.gcd_eq_one]
    exact Nat.dvd_gcd (dvd_refl h) hdN
  have := Nat.le_of_dvd (by decide : 0 < 1) hh1
  omega

/-- The two opposite unit phases have gap at least one third; quotient four
has the stronger half-circle gap. -/
theorem double_phase_gap {h V : ℕ} (hh : h=3 ∨ h=4 ∨ h=6)
    (hV : Nat.Coprime h V) :
    1/3 ≤ ndist (2*(V:ℝ)/h) ∧ (h=4 → 1/2 ≤ ndist (2*(V:ℝ)/h)) := by
  rcases hh with rfl | rfl | rfl
  · have hc : Nat.Coprime 3 (2*V) := (by decide : Nat.Coprime 3 2).mul_right hV
    have ht := one_div_le_ndist_div (m:=3) (v:=((2*V:ℕ):ℤ)) (by decide)
      (not_dvd_of_coprime (by decide : 2 ≤ 3) hc)
    push_cast at ht
    exact ⟨by simpa only [Nat.cast_ofNat] using ht,by intro hf; contradiction⟩
  · have hc : Nat.Coprime 2 V := hV.of_dvd_left (by decide : 2 ∣ 4)
    have ht := one_div_le_ndist_div (m:=2) (v:=(V:ℤ)) (by decide)
      (not_dvd_of_coprime (by decide : 2 ≤ 2) hc)
    have heq : 2*(V:ℝ)/4=(V:ℝ)/2 := by ring
    push_cast at ht
    norm_num only [Nat.cast_ofNat]
    rw [heq]
    exact ⟨by linarith,fun _ => ht⟩
  · have hc : Nat.Coprime 3 V := hV.of_dvd_left (by decide : 3 ∣ 6)
    have ht := one_div_le_ndist_div (m:=3) (v:=(V:ℤ)) (by decide)
      (not_dvd_of_coprime (by decide : 2 ≤ 3) hc)
    have heq : 2*(V:ℝ)/6=(V:ℝ)/3 := by ring
    push_cast at ht
    norm_num only [Nat.cast_ofNat]
    rw [heq]
    exact ⟨ht,by intro hf; contradiction⟩

/-- The complement of a small active fibre is initially separated from the
slow runner's active band by its opposite-phase gap. -/
theorem initial_gap {n r m q : ℕ} (F : ActiveFibre n r m q)
    (hm : 0 < m) (hn : 0 < n) (hh : F.h=3 ∨ F.h=4 ∨ F.h=6) :
    1/3-1/(n:ℝ) ≤ ndist (-(F.V:ℝ)/F.h-((q:ℝ)/((m:ℝ)*r))/n) ∧
    (F.h=4 → 1/2-1/(n:ℝ) ≤ ndist (-(F.V:ℝ)/F.h-((q:ℝ)/((m:ℝ)*r))/n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hwindow := (active_window F hm).2
  have hgap := double_phase_gap hh F.copV
  have htri := ndist_le_add (-2*(F.V:ℝ)/F.h)
    (-(F.V:ℝ)/F.h-((q:ℝ)/((m:ℝ)*r))/n)
  have heq : -2*(F.V:ℝ)/F.h-(-(F.V:ℝ)/F.h-((q:ℝ)/((m:ℝ)*r))/n)=
      (((q:ℝ)/((m:ℝ)*r))-(n:ℝ)*F.V/F.h)/n := by field_simp; ring
  rw [heq,abs_div,abs_of_pos hnR] at htri
  have hb := div_le_div_of_nonneg_right hwindow hnR.le
  have hneg : -2*(F.V:ℝ)/F.h=-(2*(F.V:ℝ)/F.h) := by ring
  rw [hneg,ndist_neg] at htri
  exact ⟨by linarith [hgap.1], fun hf => by linarith [hgap.2 hf]⟩

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

/-- A literal first exit plus strict margin yields a strict time for all
baseline and inserted speeds, including the outgoing blocker. -/
theorem escape_at_exit {n r m q u b : ℕ} {R : Finset ℕ} {e T gamma : ℝ} {J : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hb : b ∈ primitiveFlanks n r)
    (hn : (2:ℝ) < n) (hg : 0 < gamma) (he : 1 ≤ e) (hen : e < (n:ℝ)-1)
    (heq : gamma*e=T+1) (hbe : (b:ℝ)*e < (m:ℝ)*((n:ℝ)-r))
    (hphase : ∀z : ℝ, (u:ℝ)*((numerator r b:ℝ)/r-z/((n:ℝ)*m*r))=
      (J:ℝ)+(T-gamma*z)/n)
    (hq : 1/(n:ℝ) < ndist ((q:ℝ)*((numerator r b:ℝ)/r-e/((n:ℝ)*m*r)))) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  let clock : ℝ → ℝ := fun z => (numerator r b:ℝ)/r-z/((n:ℝ)*m*r)
  let U : Set ℝ := {z | z < (n:ℝ)-1 ∧ (b:ℝ)*z < (m:ℝ)*((n:ℝ)-r) ∧
    gamma*z < T+(n:ℝ)-1 ∧ 1/(n:ℝ) < ndist ((q:ℝ)*clock z)}
  have hopen : IsOpen U := by
    apply IsOpen.inter (isOpen_lt continuous_id continuous_const)
    apply IsOpen.inter (isOpen_lt (continuous_const.mul continuous_id) continuous_const)
    apply IsOpen.inter (isOpen_lt (continuous_const.mul continuous_id) continuous_const)
    exact isOpen_lt continuous_const (BadCover.continuous_ndist.comp (by fun_prop))
  have hmem : e ∈ U := ⟨hen,hbe,by linarith,hq⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen e hmem
  let z := e+ε/2
  have hze : e < z := by dsimp [z]; linarith
  have hzU : z ∈ U := hball (by
    rw [Metric.mem_ball,Real.dist_eq]
    have hdiff : z-e=ε/2 := by dsimp [z]; ring
    rw [hdiff,abs_of_pos (by positivity : 0 < ε/2)]
    linarith)
  apply SharedSlowestHalf.strict_of_clock hr hrn hm hrR hlarge hb (by linarith)
    hzU.1 hzU.2.1 hzU.2.2.2
  rw [hphase]
  have hn0 : (0:ℝ) < n := by linarith
  have hlow : -(n:ℝ)+1 < T-gamma*z := by linarith [hzU.2.2.1]
  have hhigh : T-gamma*z < -1 := by
    have hh := mul_lt_mul_of_pos_left hze hg
    linarith
  apply BadCover.strict_of_between (m:=J-1)
  · push_cast
    have hh : -1+1/(n:ℝ) < (T-gamma*z)/n := by
      apply (lt_div_iff₀ hn0).mpr
      have he : (1/(n:ℝ))*n=1 := by field_simp
      rw [add_mul,he]; linarith
    linarith
  · push_cast
    have hh : (T-gamma*z)/(n:ℝ) < -(1/(n:ℝ)) := by
      have := div_lt_div_of_pos_right hhigh hn0
      simpa only [neg_div] using this
    linarith

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

/-- Complementarity at the unit representatives implies the opposite slower
phase at every primitive representative in the faster fibre. -/
theorem opposite_phase {n r m q u b : ℕ}
    (F : ActiveFibre n r m q) (G : ActiveFibre n r m u)
    (hr : 0 < r) (hsmall : F.h=3 ∨ F.h=4 ∨ F.h=6)
    (hcomp : ∀c ∈ units r, CollectiveBoundary.Blocks (n:ℤ) r m u c →
      ¬CollectiveBoundary.Blocks (n:ℤ) r m q c)
    (hb : b ∈ primitiveFlanks n r) (hbg : (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U) :
    ∃J : ℤ, (q:ℝ)*(numerator r b:ℝ)/r=(J:ℝ)-(F.V:ℝ)/F.h := by
  have hcop := (mem_primitiveFlanks.mp hb).2.2
  have hbm : b%r ∈ units r := by
    apply mem_units.mpr
    refine ⟨Nat.mod_lt _ hr,?_⟩
    change Nat.gcd r (b%r)=1
    rw [Nat.gcd_comm,← Nat.gcd_rec]
    exact hcop
  have hdh : F.h ∣ r := ⟨F.d,by nlinarith only [F.r_eq]⟩
  have hdg : G.h ∣ r := ⟨G.d,by nlinarith only [G.r_eq]⟩
  have hnF : ¬(F.h:ℤ) ∣ (F.V:ℤ)*b-F.U := by
    intro hh
    apply hcomp (b%r) hbm
      ((G.blocks_iff _ hbm).mpr ((PrimitiveFibre.linear_mod_iff hdg).mp hbg))
    exact (F.blocks_iff _ hbm).mpr ((PrimitiveFibre.linear_mod_iff hdh).mp hh)
  have hopp := SmallFibrePhase.opposite_congruence hsmall F.copV F.copU
    (hcop.of_dvd_left hdh) hnF
  have hncong : (F.h:ℤ) ∣ (-(F.V:ℤ))*(b:ℤ)-F.U := by
    have heq : -((F.V:ℤ)*(b:ℤ)+F.U)=(-(F.V:ℤ))*(b:ℤ)-F.U := by ring
    simpa only [heq] using dvd_neg.mpr hopp
  obtain ⟨J,hJ⟩ := SmallFibrePhase.phase_lap F (numerator_unit hcop) hncong
  refine ⟨J,?_⟩
  simpa only [Int.cast_neg,Int.cast_natCast,neg_div,sub_eq_add_neg] using hJ



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
open LonelyRunner.ComplementaryEscape
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- All geometric hypotheses of an escape are derived from the active
small-fibre certificates; only the selected flank's arithmetic margin remains. -/
theorem solution {n r m q u b : ℕ} {R : Finset ℕ}
    (F : ActiveFibre n r m q) (G : ActiveFibre n r m u)
    (hr : 7 ≤ r) (hrmax : r+2 ≤ n) (hm : 0 < m) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hpq : m*r < q) (hqu : q < u)
    (hF : F.h=3 ∨ F.h=4 ∨ F.h=6) (hG : G.h=3 ∨ G.h=4 ∨ G.h=6)
    (hsize : 12 ≤ n ∨ F.h=4)
    (hcomp : ∀c ∈ units r, CollectiveBoundary.Blocks (n:ℤ) r m u c →
      ¬CollectiveBoundary.Blocks (n:ℤ) r m q c)
    (hb : b ∈ primitiveFlanks n r) (hbg : (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U)
    (hmargin : (b:ℝ)*(((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))) <
      (m:ℝ)*((n:ℝ)-r)) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by
  have hr0 : 0 < r := by omega
  have hrn : r < n := by omega
  have hn : 9 ≤ n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrR' : (0:ℝ) < r := by exact_mod_cast hr0
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hgn : G.h < n := by rcases hG with hh | hh | hh <;> omega
  let slow : ℝ := (q:ℝ)/((m:ℝ)*r)
  let fast : ℝ := (u:ℝ)/((m:ℝ)*r)
  let T : ℝ := (n:ℝ)*G.V/G.h
  let e : ℝ := (T+1)/fast
  have hslow : 0 < slow := div_pos (by exact_mod_cast (show 0 < q by omega)) (by positivity)
  have horder : slow < fast := div_lt_div_of_pos_right (by exact_mod_cast hqu) (by positivity)
  have hfast : 0 < fast := hslow.trans horder
  have hbounds := exit_bounds G hm (by omega) hgn (by omega : 0 < u)
  have hZ : ((n:ℝ)+G.h)/((n:ℝ)-G.h) < (n:ℝ)-1 := by
    have hhh : (0:ℝ) ≤ G.h := by positivity
    have hhmax : (G.h:ℝ)+2 < n := by
      have ht : G.h+2 < n := by
        rcases hG with hh | hh | hh <;> omega
      exact_mod_cast ht
    apply (div_lt_iff₀ (by linarith : (0:ℝ) < n-G.h)).mpr
    nlinarith [mul_pos hnR (show 0 < (n:ℝ)-G.h-2 by linarith)]
  obtain ⟨J,hJ⟩ := opposite_phase F G hr0 hF hcomp hb hbg
  obtain ⟨K,hK⟩ := SmallFibrePhase.phase_lap G
    (numerator_unit (mem_primitiveFlanks.mp hb).2.2) hbg
  push_cast at hK
  have hgap := SmallFibrePhase.initial_gap F hm (by omega) hF
  have hsafe : 1/(n:ℝ) < ndist (-(F.V:ℝ)/F.h-slow*e/n) := by
    rcases hsize with hn12 | hf4
    · exact TwoBlockerGeometry.no_handoff_thirds (by exact_mod_cast hn12) hslow horder
        hbounds.1 hbounds.2.2 hgap.1
    · exact TwoBlockerGeometry.no_handoff_halves (by exact_mod_cast (show 8 ≤ n by omega)) hslow horder
        hbounds.1 hbounds.2.2 (hgap.2 hf4)
  apply escape_at_exit hr0 hrn hm hrR hlarge hb (by exact_mod_cast (show 2 < n by omega))
    hfast hbounds.1 (hbounds.2.1.trans_lt hZ) (show fast*e=T+1 by dsimp [e]; field_simp)
    hmargin
  · intro z
    rw [mul_sub,← mul_div_assoc,hK]
    dsimp [T,fast]
    field_simp
    ring
  · have heq : (q:ℝ)*((numerator r b:ℝ)/r-e/((n:ℝ)*m*r))=
        (J:ℝ)+(-(F.V:ℝ)/F.h-slow*e/n) := by
      rw [mul_sub,← mul_div_assoc,hJ]
      dsimp [slow]; field_simp; ring
    change 1/(n:ℝ) < ndist ((q:ℝ)*((numerator r b:ℝ)/r-e/((n:ℝ)*m*r)))
    rw [heq,ndist_int_add]
    exact hsafe
