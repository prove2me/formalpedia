-- Prove2me | solution 1 for LonelyRunner.CollectiveSecondFastest.clock_exit_escape
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:11:44.016393+00:00
-- url     : https://prove2.me/submissions/4ce2b167-5e51-4056-a7d4-3c953b265a8c

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

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
open LonelyRunner.CollectiveSecondFastest
open BadCover

/-- Strict inequalities at finitely many speeds persist on a small rightward
clock interval. Both distinguished runners become safe immediately after the
common exit. -/
theorem solution {n P Q gamma z₀ T : ℝ} {A J j : ℤ}
    (S : Finset ℕ) (clock : ℝ → ℝ) (hclock : Continuous clock)
    (hn : 2 < n) (hg : 0 < gamma)
    (hz : 1 ≤ z₀) (hzupper : z₀ < n-1)
    (he : gamma*z₀=T+1) (hT : T=n*((j:ℝ)+1/2))
    (hP : ∀ z, P*clock z=(A:ℝ)-z/n)
    (hQ : ∀ z, Q*clock z=(J:ℝ)+1/2-gamma*z/n)
    (hsafe : ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z₀)) :
    ∃ z, z₀ < z ∧ 1/n < ndist (P*clock z) ∧
      1/n < ndist (Q*clock z) ∧ ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z) := by
  let U : Set ℝ := {z | z < n-1 ∧ gamma*z < T+n-1 ∧
      ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z)}
  have hopen : IsOpen U := by
    apply IsOpen.inter (isOpen_lt continuous_id continuous_const)
    apply IsOpen.inter (isOpen_lt (continuous_const.mul continuous_id) continuous_const)
    change IsOpen {z | ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z)}
    simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun v _ =>
      isOpen_lt continuous_const (continuous_ndist.comp (continuous_const.mul hclock))
  have hmem : z₀ ∈ U := ⟨hzupper, by linarith, hsafe⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen z₀ hmem
  let z := z₀+ε/2
  have hzz : z₀ < z := by dsimp [z]; linarith
  have hzU : z ∈ U := hball (by
    rw [Metric.mem_ball,Real.dist_eq]
    have : z-z₀=ε/2 := by dsimp [z]; ring
    rw [this,abs_of_pos (by positivity : 0 < ε/2)]
    linarith)
  have hn0 : 0 < n := by linarith
  refine ⟨z,hzz,?_,?_,hzU.2.2⟩
  · rw [hP]
    apply strict_of_between (m := A-1)
    · push_cast
      have hh : z/n < 1-1/n := by
        apply (div_lt_iff₀ hn0).mpr
        have hnn : (1/n)*n=1 := by field_simp
        rw [sub_mul,one_mul,hnn]
        exact hzU.1
      linarith
    · push_cast
      have hh : 1/n < z/n := (div_lt_div_iff_of_pos_right hn0).mpr (by linarith)
      linarith
  · rw [hQ]
    apply strict_of_between (m := J-j-1)
    · push_cast
      have hh : gamma*z/n < ((j:ℝ)+1/2)+1-1/n := by
        apply (div_lt_iff₀ hn0).mpr
        have hnz : (1/n)*n=1 := by field_simp
        rw [sub_mul,add_mul,hnz]
        have hhi := hzU.2.1
        rw [hT] at hhi
        nlinarith
      linarith
    · push_cast
      have hh : ((j:ℝ)+1/2)+1/n < gamma*z/n := by
        apply (lt_div_iff₀ hn0).mpr
        have hnz : (1/n)*n=1 := by field_simp
        rw [add_mul,hnz]
        have hm := mul_lt_mul_of_pos_left hzz hg
        rw [hT] at he
        nlinarith
      linarith
