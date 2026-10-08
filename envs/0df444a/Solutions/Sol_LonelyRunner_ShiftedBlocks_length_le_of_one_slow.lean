-- Prove2me | solution 1 for LonelyRunner.ShiftedBlocks.length_le_of_one_slow
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T06:11:46.757607+00:00
-- url     : https://prove2.me/submissions/04111ead-7f83-4b2c-b1ef-9fbd88d4638b

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

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

theorem single_band {A B w β δ : ℝ} (hw : 0 < w) (hδ : δ < 1/2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (β+w*t) ≤ δ) :
    ∃ k : ℤ, ∀ t ∈ Set.Icc A B, |β+w*t-k| ≤ δ := by
  let k : ℤ := round (β+w*A)
  have hA : |β+w*A-k| ≤ δ := hcover A ⟨le_rfl,hAB⟩
  have hAl := (abs_le.mp hA).1
  have hAu := (abs_le.mp hA).2
  have hB : β+w*B < k+1/2 := by
    by_contra! hb
    let t := ((k:ℝ)+1/2-β)/w
    have ht : t ∈ Set.Icc A B := by
      dsimp [t]
      constructor
      · apply (le_div_iff₀ hw).2; linarith
      · apply (div_le_iff₀ hw).2; linarith
    have hc := hcover t ht
    have heq : β+w*t=k+1/2 := by dsimp [t]; field_simp; ring
    rw [heq,ndist_int_add,ndist_half] at hc
    linarith
  refine ⟨k,fun t ht => ?_⟩
  have heq : round (β+w*t)=k := by
    apply round_eq_iff.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hw.le,
      mul_le_mul_of_nonneg_left ht.2 hw.le]
  simpa only [ndist,heq] using hcover t ht



















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
open LonelyRunner.ShiftedBlocks

theorem solution {A B p q α β δ u : ℝ} {c : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ : δ < 1/2)
    (hu : u ∈ Set.Icc A B) (hc : |α+p*u-c| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |α+p*t-c| ≤ δ ∨ ndist (β+q*t) ≤ δ) :
    B-A ≤ blockBound p q δ := by
  let L := ((c:ℝ)-α-δ)/p
  let R := ((c:ℝ)-α+δ)/p
  let a := 2*δ/p
  let b := 2*δ/q
  have hL : p*L=(c:ℝ)-α-δ := by dsimp [L]; field_simp
  have hR : p*R=(c:ℝ)-α+δ := by dsimp [R]; field_simp
  have hlen : R-L=a := by dsimp [R,L,a]; field_simp; ring
  have hqb : q*b=2*δ := by dsimp [b]; field_simp
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hlu : L ≤ u := by nlinarith [(abs_le.mp hc).1]
  have hur : u ≤ R := by nlinarith [(abs_le.mp hc).2]
  have hclosed : IsClosed {t : ℝ | ndist (β+q*t) ≤ δ} :=
    isClosed_le (BadCover.continuous_ndist.comp
      (continuous_const.add (continuous_const.mul continuous_id))) continuous_const
  have hleft (hAL : A < L) : ∃ j : ℤ, ∀ t ∈ Set.Icc A L, |β+q*t-j| ≤ δ := by
    have hsub : Set.Ico A L ⊆ {t : ℝ | ndist (β+q*t) ≤ δ} := by
      intro t ht
      have hnot : ¬ |α+p*t-c| ≤ δ := by
        intro hh
        nlinarith [(abs_le.mp hh).1,mul_lt_mul_of_pos_left ht.2 hp]
      exact (hcover t ⟨ht.1,by linarith [hu.2,ht.2]⟩).resolve_left hnot
    have hcl := closure_minimal hsub hclosed
    rw [closure_Ico hAL.ne] at hcl
    exact single_band hq hδ hAL.le (fun t ht => hcl ht)
  have hright (hRB : R < B) : ∃ k : ℤ, ∀ t ∈ Set.Icc R B, |β+q*t-k| ≤ δ := by
    have hsub : Set.Ioc R B ⊆ {t : ℝ | ndist (β+q*t) ≤ δ} := by
      intro t ht
      have hnot : ¬ |α+p*t-c| ≤ δ := by
        intro hh
        nlinarith [(abs_le.mp hh).2,mul_lt_mul_of_pos_left ht.1 hp]
      exact (hcover t ⟨by linarith [hu.1,ht.1],ht.2⟩).resolve_left hnot
    have hcl := closure_minimal hsub hclosed
    rw [closure_Ioc hRB.ne] at hcl
    exact single_band hq hδ hRB.le (fun t ht => hcl ht)
  have hAb : L-b ≤ A := by
    by_cases hAL : A < L
    · obtain ⟨j,hj⟩ := hleft hAL
      have ha := (abs_le.mp (hj A ⟨le_rfl,hAL.le⟩)).1
      have hl := (abs_le.mp (hj L ⟨hAL.le,le_rfl⟩)).2
      nlinarith
    · linarith
  have hBb : B ≤ R+b := by
    by_cases hRB : R < B
    · obtain ⟨k,hk⟩ := hright hRB
      have hr := (abs_le.mp (hk R ⟨le_rfl,hRB.le⟩)).1
      have hb := (abs_le.mp (hk B ⟨hRB.le,le_rfl⟩)).2
      nlinarith
    · linarith
  by_cases hAL : L ≤ A
  · apply le_trans (show B-A ≤ a+b by linarith) (le_max_left _ _)
  by_cases hBR : B ≤ R
  · apply le_trans (show B-A ≤ a+b by linarith) (le_max_left _ _)
  have hAL' : A < L := lt_of_not_ge hAL
  have hRB : R < B := lt_of_not_ge hBR
  obtain ⟨j,hj⟩ := hleft hAL'
  obtain ⟨k,hk⟩ := hright hRB
  have ha := (abs_le.mp (hj A ⟨le_rfl,hAL'.le⟩)).1
  have hl := (abs_le.mp (hj L ⟨hAL'.le,le_rfl⟩)).2
  have hr := (abs_le.mp (hk R ⟨le_rfl,hRB.le⟩)).1
  have hb := (abs_le.mp (hk B ⟨hRB.le,le_rfl⟩)).2
  have hdiff : ((k-j:ℤ):ℝ) ≤ q*(a+b) := by
    push_cast
    nlinarith [congrArg (fun z : ℝ => q*z) hlen]
  have hfloor : k-j ≤ ⌊q*(a+b)⌋ := Int.le_floor.mpr hdiff
  have hfloorR : (k:ℝ)-j ≤ (⌊q*(a+b)⌋:ℤ) := by exact_mod_cast hfloor
  have hbound : B-A ≤ (((⌊q*(a+b)⌋:ℤ):ℝ)+2*δ)/q := by
    apply (le_div_iff₀ hq).2
    nlinarith
  exact le_trans hbound (le_max_right _ _)
