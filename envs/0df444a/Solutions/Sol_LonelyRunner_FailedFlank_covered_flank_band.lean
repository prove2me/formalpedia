-- Prove2me | solution 1 for LonelyRunner.FailedFlank.covered_flank_band
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:29.686112+00:00
-- url     : https://prove2.me/submissions/0af3dab4-13db-4460-b990-d8c667ad32eb

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm





theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x



@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]



@[simp] theorem ndist_neg (x : ℝ) : ndist (-x) = ndist x := by
  rw [ndist_eq_norm, ndist_eq_norm, AddCircle.coe_neg, norm_neg]





theorem ndist_int_sub (x : ℝ) (m : ℤ) : ndist (m - x) = ndist x := by
  rw [sub_eq_add_neg, ndist_int_add, ndist_neg]

/-- On `[0, 1/2]` the distance to the nearest integer is the identity. -/
theorem ndist_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ndist x = x := by
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨h0, by linarith⟩
  rw [ndist_eq_min_fract, hfr]
  exact min_eq_left (by linarith)

@[simp] theorem ndist_half : ndist (1 / 2) = 1 / 2 := ndist_of_mem (by norm_num) le_rfl

















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

/-- A whole interval of bad times for one positive speed stays in one band. -/
theorem single_band {A B w δ : ℝ} (hw : 0 < w) (hδ : δ < 1 / 2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (w * t) ≤ δ) :
    ∃ k : ℤ, ∀ t ∈ Set.Icc A B, |w * t - k| ≤ δ := by
  let k : ℤ := round (w * A)
  have hA : |w * A - k| ≤ δ := hcover A ⟨le_rfl, hAB⟩
  have hAl := (abs_le.mp hA).1
  have hAu := (abs_le.mp hA).2
  have hB : w * B < k + 1 / 2 := by
    by_contra! hb
    let t := ((k : ℝ) + 1 / 2) / w
    have ht : t ∈ Set.Icc A B := by
      dsimp [t]
      constructor
      · apply (le_div_iff₀ hw).mpr
        nlinarith
      · apply (div_le_iff₀ hw).mpr
        nlinarith
    have hc := hcover t ht
    have hwt : w * t = k + 1 / 2 := by dsimp [t]; field_simp
    rw [hwt, ndist_int_add, ndist_half] at hc
    linarith
  refine ⟨k, fun t ht => ?_⟩
  have hround : round (w * t) = k := by
    apply round_eq_iff.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hw.le,
      mul_le_mul_of_nonneg_left ht.2 hw.le]
  simpa only [ndist, hround] using hcover t ht













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



theorem cover_of_no_strict {n r s p q : ℕ} (h : ¬ HasStrictTime n r s p q)
    {t : ℝ} (hret : ∀ v : ℕ, 0 < v → v < n → v ≠ r → v ≠ s →
      (1:ℝ)/n  <  ndist ((v:ℝ)*t)) :
    ndist ((p:ℝ)*t)  ≤  1/n ∨ ndist ((q:ℝ)*t)  ≤  1/n := by
  by_contra! hh
  apply h
  refine ⟨t,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvr,hvs⟩ | rfl | rfl
  · simpa only [mul_comm] using hret v hv hvn hvr hvs
  · simpa only [mul_comm] using hh.1
  · simpa only [mul_comm] using hh.2















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
open LonelyRunner.FailedFlank
open Farey BadCover LargeDeletionMatching

set_option maxHeartbeats 1200000 in
/-- If the whole instance has no strict time, one q-band covers both ends
of every canonical failed flank, not merely the nearer endpoint. -/
theorem solution {n r s m b q : ℕ} {a c : ℤ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hmn : m+1 ≤ n) (hq : 0 < q)
    (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hunit : a*(b:ℤ)-c*(r:ℤ)=1)
    (hno : ¬ HasStrictTime n r s (m*r) q) :
    ∃ j : ℤ,
      |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n ∧
      |(q:ℝ)*((a:ℝ)/r-((n:ℝ)-r)/((n:ℝ)*r*b))-j| ≤ 1/n := by
  have hr : 0 < r := by omega
  have hb : 0 < b := by omega
  have hnR : (0:ℝ) < n := by positivity
  have hrR : (0:ℝ) < r := by positivity
  have hbR : (0:ℝ) < b := by positivity
  have hmR : (0:ℝ) < m := by positivity
  have hqR : (0:ℝ) < q := by positivity
  have habR : (n:ℝ)-r ≤ b := by
    rw [← Nat.cast_sub hrn.le]
    exact_mod_cast hab
  have hfailR : (b:ℝ) < (m:ℝ)*((n:ℝ)-r) := by
    rw [← Nat.cast_sub hrn.le]
    exact_mod_cast hfail
  let x : ℝ := (a:ℝ)/r
  let E : ℝ := ((n:ℝ)-r)/((n:ℝ)*r*b)
  let e₀ : ℝ := 1/((n:ℝ)*m*r)
  have he0 : 0 < e₀ := by dsimp [e₀]; positivity
  have hE : e₀ < E := by
    dsimp [e₀,E]
    rw [div_lt_div_iff₀ (mul_pos (mul_pos hnR hmR) hrR)
      (mul_pos (mul_pos hnR hrR) hbR)]
    nlinarith only [mul_lt_mul_of_pos_left hfailR (mul_pos hnR hrR)]
  have hEmax : E ≤ 1/((n:ℝ)*r) := by
    dsimp [E]
    rw [div_le_div_iff₀ (mul_pos (mul_pos hnR hrR) hbR) (mul_pos hnR hrR)]
    nlinarith only [mul_le_mul_of_nonneg_left habR (mul_pos hnR hrR).le]
  have hcov : Set.Ioo (x-E) (x-e₀) ⊆ {t : ℝ | ndist ((q:ℝ)*t) ≤ 1/n} := by
    intro t ht
    let e := x-t
    have he : e₀ < e := by dsimp [e]; linarith [ht.2]
    have heE : e < E := by dsimp [e]; linarith [ht.1]
    have hepos : 0 < e := lt_trans he0 he
    have hemax := lt_of_lt_of_le heE hEmax
    have heb : e*b < ((n:ℝ)-r)/((n:ℝ)*r) := by
      have hh := mul_lt_mul_of_pos_right heE hbR
      have hid : E*(b:ℝ)=((n:ℝ)-r)/((n:ℝ)*r) := by dsimp [E]; field_simp
      rwa [hid] at hh
    have hret (v : ℕ) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
        (1:ℝ)/n < ndist ((v:ℝ)*t) := by
      have hh := baseline_safe_offset (n := (n:ℤ)) (r := (r:ℤ))
        (b := (b:ℤ)) (a := a) (c := c) (v := (v:ℤ))
        (by exact_mod_cast hr) (by exact_mod_cast hrn) (by exact_mod_cast hlarge)
        (by exact_mod_cast habR) hunit (by exact_mod_cast hv)
        (by exact_mod_cast hvn) (by exact_mod_cast hne) hepos hemax heb
      simpa [e,x] using hh
    have hp : (1:ℝ)/n < ndist (((m*r:ℕ):ℝ)*t) := by
      have hlo : (1:ℝ)/n < ((m:ℝ)*r)*e := by
        have hh := mul_lt_mul_of_pos_left he (mul_pos hmR hrR)
        have hid : ((m:ℝ)*r)*e₀ = 1/n := by dsimp [e₀]; field_simp
        rwa [hid] at hh
      have hhi : ((m:ℝ)*r)*e < 1-(1:ℝ)/n := by
        have hh := mul_lt_mul_of_pos_left hemax (mul_pos hmR hrR)
        have hid : ((m:ℝ)*r)*(1/((n:ℝ)*r)) = (m:ℝ)/n := by field_simp
        rw [hid] at hh
        have hmnr : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
        have hle : (m:ℝ)/n ≤ 1-(1:ℝ)/n := by
          apply (div_le_iff₀ hnR).mpr
          field_simp
          linarith only [hmnr]
        exact lt_of_lt_of_le hh hle
      have hid : ((m*r:ℕ):ℝ)*t = (m*a:ℤ)-((m:ℝ)*r)*e := by
        dsimp [e,x]
        push_cast
        field_simp
        ring
      rw [hid,ndist_int_sub]
      exact strict_of_between (m := 0) (by simpa using hlo) (by simpa using hhi)
    exact (cover_of_no_strict hno (fun v hv hvn hvr _ => hret v hv hvn hvr)).resolve_left
      (not_le.mpr hp)
  have hclosed : IsClosed {t : ℝ | ndist ((q:ℝ)*t) ≤ 1/n} :=
    isClosed_le (continuous_ndist.comp (continuous_const.mul continuous_id)) continuous_const
  have hc := closure_minimal hcov hclosed
  rw [closure_Ioo (by linarith : x-E ≠ x-e₀)] at hc
  have hsmall : (1:ℝ)/n < 1/2 := by
    rw [div_lt_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)]
    have : (5:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨j,hj⟩ := single_band hqR hsmall (by linarith : x-E ≤ x-e₀) hc
  exact ⟨j,hj _ ⟨by linarith,le_rfl⟩,hj _ ⟨le_rfl,by linarith⟩⟩
