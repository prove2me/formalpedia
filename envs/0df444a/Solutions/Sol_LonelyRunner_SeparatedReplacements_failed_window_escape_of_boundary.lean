-- Prove2me | solution 1 for LonelyRunner.SeparatedReplacements.failed_window_escape_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:33.658982+00:00
-- url     : https://prove2.me/submissions/9f1e9631-b36e-4f93-91b3-40852eeab408

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_FailedWindow_baseline_safe_boundary

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm











































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

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

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







/-- Strict safety for finitely many other speeds survives moving just beyond
the left endpoint of a bad band. -/
theorem escape_left {p δ t : ℝ} {c : ℤ} (S : Finset ℕ)
    (hp : 0<p) (hδ : δ<1/2) (hc : p*t=(c:ℝ)-δ)
    (hsafe : ∀ v∈S, δ<ndist ((v:ℝ)*t)) :
    ∃ u : ℝ, δ<ndist (p*u) ∧ ∀ v∈S, δ<ndist ((v:ℝ)*u) := by
  have hopen : IsOpen {u : ℝ | ∀ v∈S, δ<ndist ((v:ℝ)*u)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun v _ =>
      isOpen_lt continuous_const (continuous_ndist.comp (continuous_const.mul continuous_id))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen t hsafe
  let e := min (ε/2) ((1-2*δ)/(2*p))
  have he : 0<e := lt_min (by positivity) (by apply div_pos <;> linarith)
  have heε : e<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hep : p*e≤(1-2*δ)/2 := by
    have hh := (le_div_iff₀ (show 0<2*p by linarith)).mp (min_le_right (ε/2) ((1-2*δ)/(2*p)))
    dsimp [e]
    nlinarith only [hh]
  refine ⟨t-e,?_,hball ?_⟩
  · apply strict_of_between (m := c-1)
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  · rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos he]
    exact heε

end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover



/-- The inserted speed is exactly at the left boundary used above. -/
theorem boundary_value {n r m a : ℤ} (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) :
    ((m*r:ℤ):ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)) = (m*a:ℤ)-(1:ℝ)/n := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp





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
open LonelyRunner.SeparatedReplacements
open LargeDeletionMatching SeparatedBands

set_option maxHeartbeats 1000000 in
/-- Turn any strictly safe failed-window boundary into a strict time. -/
theorem solution {n r s m z b : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m)
    (hab : n-r ≤ b) (hfail : b < m*(n-r)) (hcop : Nat.Coprime r b)
    (hsafe : ∀ a c : ℤ, a*(b:ℤ)-c*(r:ℤ)=1 →
      (1:ℝ)/n < ndist ((z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)))) :
    HasStrictTime n r s (m*r) z := by
  have hr : 0 < r := by omega
  have hrZ : (0:ℤ) < r := by exact_mod_cast hr
  have hnZ : (0:ℤ) < n := by omega
  have hmZ : (0:ℤ) < m := by omega
  have hrR : (0:ℝ) < r := by positivity
  have hnR : (0:ℝ) < n := by positivity
  have hmR : (0:ℝ) < m := by positivity
  have hpR : (0:ℝ) < (m:ℝ)*r := mul_pos hmR hrR
  have hδ : (0:ℝ) < 1/n := by positivity
  have hsmall : (1:ℝ)/n < 1/2 := by
    apply (div_lt_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)).mpr
    have : (5:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨a',c',hunit'⟩ := Farey.exists_determinant_one
    (r := (r:ℤ)) (s := (b:ℤ)) (by simpa using hcop.gcd_eq_one)
  let a := -a'
  let c := -c'
  have hunit : a*(b:ℤ)-c*(r:ℤ)=1 := by dsimp [a,c]; nlinarith only [hunit']
  let t : ℝ := (a:ℝ)/r-1/((n:ℝ)*m*r)
  have hval : ((m*r:ℕ):ℝ)*t=(m*a:ℤ)-(1:ℝ)/n := by
    simpa [t] using FailedWindow.boundary_value (a := a) hnZ hrZ hmZ
  have hzsafe := hsafe a c hunit
  have hbase (v : ℕ) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
      (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    apply FailedWindow.baseline_safe_boundary (n := (n:ℤ)) (r := (r:ℤ)) (m := (m:ℤ))
      (b := (b:ℤ)) (a := a) (c := c) hrZ (by exact_mod_cast hrn)
      (by exact_mod_cast hlarge) (by omega)
    · rw [← Nat.cast_sub hrn.le]
      exact_mod_cast hab
    · rw [← Nat.cast_sub hrn.le]
      exact_mod_cast hfail
    · exact hunit
    · exact_mod_cast hv
    · exact_mod_cast hvn
    · exact_mod_cast hne
  let S := insert z ((Finset.range n).filter (fun v => 0 < v ∧ v ≠ r ∧ v ≠ s))
  have hS : ∀ v∈S, (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hzsafe
    · obtain ⟨hv,hv0,hvr,_⟩ := Finset.mem_filter.mp hv
      exact hbase v hv0 (Finset.mem_range.mp hv) hvr
  obtain ⟨u,hp,hu⟩ := escape_left S (by exact_mod_cast hpR) hsmall hval hS
  refine ⟨u,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvr,hvs⟩ | rfl | rfl
  · have hvS : v∈S := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvn,hv,hvr,hvs⟩)
    simpa only [mul_comm] using hu v hvS
  · simpa only [mul_comm] using hp
  · simpa only [mul_comm] using hu _ (Finset.mem_insert_self _ _)
