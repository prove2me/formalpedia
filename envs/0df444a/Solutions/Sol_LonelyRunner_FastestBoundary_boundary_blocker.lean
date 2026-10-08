-- Prove2me | solution 1 for LonelyRunner.FastestBoundary.boundary_blocker
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:09:14.384837+00:00
-- url     : https://prove2.me/submissions/5a0758b1-7def-4f45-b58d-cb5380f44dfa

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs
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
open LonelyRunner.FastestBoundary

/-- If no strict time exists, some other insertion blocks every failed boundary.
There is no separation or cardinality hypothesis. -/
theorem solution {n r m b : ℕ} {a c : ℤ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    ∃ q ∈ W.erase (m*r),
      ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) ≤ 1/n := by
  by_contra! hh
  have hr : 0 < r := by omega
  have hm0 : 0 < m := by omega
  have hnR : (0:ℝ) < n := by positivity
  let t : ℝ := (a:ℝ)/r-1/((n:ℝ)*m*r)
  have hval : ((m*r:ℕ):ℝ)*t=(m*a:ℤ)-(1:ℝ)/n := by
    have hrR : (r:ℝ) ≠ 0 := by positivity
    have hmR : (m:ℝ) ≠ 0 := by positivity
    dsimp [t]
    push_cast
    field_simp
  have hbase (v : ℕ) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
      (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    apply FailedWindow.baseline_safe_boundary (n := (n:ℤ)) (r := (r:ℤ))
      (m := (m:ℤ)) (b := (b:ℤ)) (a := a) (c := c)
      (by exact_mod_cast hr) (by exact_mod_cast hrn) (by exact_mod_cast hlarge) (by omega)
    · rw [← Nat.cast_sub hrn.le]; exact_mod_cast hab
    · rw [← Nat.cast_sub hrn.le]; exact_mod_cast hfail
    · exact hu
    · exact_mod_cast hv
    · exact_mod_cast hvn
    · exact_mod_cast hne
  let S := ((Finset.range n).filter (fun v => 0 < v ∧ v ∉ R)) ∪ W.erase (m*r)
  have hS : ∀ v ∈ S, (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hvn,hv0,hvR⟩ := Finset.mem_filter.mp hv
      exact hbase v hv0 (Finset.mem_range.mp hvn) (by rintro rfl; exact hvR hrR)
    · exact hh v hv
  have hhalf : (1:ℝ)/n < 1/2 := by
    apply (div_lt_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)).mpr
    exact_mod_cast (show 1*2 < 1*n by omega)
  obtain ⟨u,hp,huS⟩ := SeparatedBands.escape_left S
    (by exact_mod_cast Nat.mul_pos hm0 hr) hhalf hval hS
  apply hno
  refine ⟨u,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hvW
  · exact huS v (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hvn,hv,hvR⟩))
  · by_cases heq : v=m*r
    · simpa [heq] using hp
    · exact huS v (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨heq,hvW⟩))
