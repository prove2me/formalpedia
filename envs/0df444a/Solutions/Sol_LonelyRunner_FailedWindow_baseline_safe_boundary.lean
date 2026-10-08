-- Prove2me | solution 1 for LonelyRunner.FailedWindow.baseline_safe_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:07:43.074983+00:00
-- url     : https://prove2.me/submissions/21709de4-ec18-4728-ad3e-fb2d31557c34

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

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
open LonelyRunner.FailedWindow
open Farey BadCover

set_option maxHeartbeats 1000000 in
/-- If b is a unit modulo r in the failed GW window, the left endpoint of
an mr-band is strictly safe for every retained baseline speed. -/
theorem solution {n r m b a c v : ℤ}
    (hr : 0 < r) (hrn : r < n) (hlarge : n ≤ 2*r) (hm : 1 ≤ m)
    (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hunit : a*b-c*r=1)
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
    (1:ℝ)/n < ndist ((v:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) := by
  let j := (v*a)%r
  let k := (v*a)/r
  have hj0 : 0 ≤ j := Int.emod_nonneg _ hr.ne'
  have hjr : j < r := Int.emod_lt_of_pos _ hr
  have hsplit : v*a=k*r+j := by
    have hh := Int.emod_add_ediv_mul (v*a) r
    dsimp [j,k]
    linarith
  have hnotdvd := retained_not_dvd hr hlarge hv hvn hne
  have hj : 1 ≤ j := by
    have hne0 : j ≠ 0 := by
      intro hz
      apply hnotdvd
      refine ⟨b*k-c*v,?_⟩
      nlinarith [congrArg (fun z : ℤ => z*v) hunit]
    omega
  have hone : j=1 → v ≤ b := by
    intro hj1
    have hd : r ∣ v-b := by
      refine ⟨b*k-c*v,?_⟩
      nlinarith [congrArg (fun z : ℤ => z*v) hunit]
    by_contra! hh
    have hge := Int.le_abs_of_dvd (by omega : v-b ≠ 0) hd
    rw [abs_of_pos (by omega : 0 < v-b)] at hge
    omega
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_trans hr hrn)
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have hvnR : (v:ℝ) < n := by exact_mod_cast hvn
  have hrnR : (r:ℝ) < n := by exact_mod_cast hrn
  have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hjrR : (j:ℝ) ≤ r-1 := by
    have : (j:ℝ)+1 ≤ r := by exact_mod_cast hjr
    linarith
  have hsplitR : (v:ℝ)*a=(k:ℝ)*r+j := by exact_mod_cast hsplit
  have heq : (v:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)) =
      k+(j:ℝ)/r-(v:ℝ)/((n:ℝ)*m*r) := by
    calc
      _ = ((v:ℝ)*a)/r-(v:ℝ)/((n:ℝ)*m*r) := by ring
      _ = _ := by rw [hsplitR,add_div,mul_div_cancel_right₀ _ hrR.ne']
  rw [heq]
  apply strict_of_between (m := k)
  · have hnum : (m:ℝ)*r < (n:ℝ)*m*j-v := by
      by_cases hj1 : j=1
      · have hvbR : (v:ℝ) ≤ b := by exact_mod_cast (hone hj1)
        have hfailR : (b:ℝ) < (m:ℝ)*((n:ℝ)-r) := by exact_mod_cast hfail
        rw [hj1]
        push_cast
        nlinarith
      · have hj2R : (2:ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
        have hbase : (n:ℝ) < (n:ℝ)*j-r := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hmR (show 0 ≤ (n:ℝ)*j-r by linarith)
        nlinarith
    have hineq : (1:ℝ)/n < (j:ℝ)/r-(v:ℝ)/((n:ℝ)*m*r) := by
      apply (mul_lt_mul_iff_right₀ (mul_pos (mul_pos hnR hm0) hrR)).mp
      field_simp
      nlinarith only [hnum]
    linarith
  · have hineq : (j:ℝ)/r < 1-(1:ℝ)/n := by
      apply (div_lt_iff₀ hrR).mpr
      apply (mul_lt_mul_iff_right₀ hnR).mp
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hjrR hnR.le]
    have : (0:ℝ) < (v:ℝ)/((n:ℝ)*m*r) := by positivity
    linarith
