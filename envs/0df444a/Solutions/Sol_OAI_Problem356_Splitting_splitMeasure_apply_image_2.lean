-- Prove2me | solution 2 for OAI.Problem356.Splitting.splitMeasure_apply_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:22:59.621195+00:00
-- url     : https://prove2.me/submissions/edf69125-32a2-446c-bd1b-f3f6963ec570

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean:L99-L124
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Splitting.splitMeasure_apply_image. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Theorems.Thm_OAI_Problem356_Splitting_map_image_eq

-- ---- from OAI.Analysis.CoulombTransport.SplitMeasure ----
namespace OAI

universe uAlpha uIndex

/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- A measure supported almost everywhere on `B` vanishes on any set disjoint from `B`. -/
theorem measure_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hBS : Disjoint B S) : ν S = 0 := by
  apply measure_mono_null (t := Bᶜ)
  · intro x hx
    exact fun hxB => Set.disjoint_left.mp hBS hxB hx
  · exact ae_iff.mp hν

/-- A branch pushforward vanishes away from the image of the central component. -/
theorem map_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hS : MeasurableSet S) (hBS : Disjoint (H '' B) S) :
    (Measure.map H ν) S = 0 := by
  rw [Measure.map_apply hH hS]
  apply measure_eq_zero_of_disjoint ν hν
  exact Set.disjoint_left.mpr fun x hxB hxS =>
    Set.disjoint_left.mp hBS ⟨x, hxB, rfl⟩ hxS

variable [Fintype ι]

/-- On one branch image only that branch summand contributes. -/
theorem splitMeasure_apply_image
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    splitMeasure ν a b H (H j '' S) = b j * ν S := by
  classical
  have hsub : H j '' S ⊆ H j '' B := Set.image_mono hSB
  have hz : ν (H j '' S) = 0 :=
    measure_eq_zero_of_disjoint ν hν ((hCentral j).mono_right hsub)
  have hij : ∀ i, i ≠ j → (Measure.map (H i) ν) (H j '' S) = 0 := by
    intro i hne
    exact map_eq_zero_of_disjoint ν hν (hH i) (hImage j)
      ((hPair hne).mono_right hsub)
  have hj : (Measure.map (H j) ν) (H j '' S) = ν S :=
    map_image_eq ν hν (hH j) (hInj j) hSB (hImage j)
  simp only [splitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, hz, mul_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · exact congrArg (b j * ·) hj
  · intro i _ hne
    simp [hij i hne]
  · simp

end Splitting
end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Splitting
open MeasureTheory Set
open scoped ENNReal


theorem solution.{uAlpha,uIndex} : type_of% @_root_.OAI.Problem356.Splitting.splitMeasure_apply_image.{uAlpha,uIndex} := @_root_.OAI.Problem356.Splitting.splitMeasure_apply_image.{uAlpha,uIndex}
