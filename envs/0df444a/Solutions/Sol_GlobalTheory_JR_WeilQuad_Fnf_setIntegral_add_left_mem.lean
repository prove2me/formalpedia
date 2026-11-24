-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.setIntegral_add_left_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:57.051749+00:00
-- url     : https://prove2.me/submissions/b8c0b641-b230-4ad7-a894-4c82e56e1a51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V)
    (hΛ : MeasurableSet (Λ : Set V)) (g : V → ℂ) (w : V) (hw : w ∈ Λ) :
    ∫ y in (Λ : Set V), g (w + y) ∂μ = ∫ y in (Λ : Set V), g y ∂μ := by
  rw [← integral_indicator hΛ, ← integral_indicator hΛ]
  have : (Set.indicator (Λ : Set V) fun y => g (w + y)) = fun y => Set.indicator (Λ : Set V) g (w + y) := by
    funext y
    by_cases hy : y ∈ Λ
    · have h2 : w + y ∈ Λ := Λ.add_mem hw hy
      simp [Set.indicator_apply, hy, h2]
    · have h2 : w + y ∉ Λ := fun h => hy (by simpa using Λ.sub_mem h hw)
      simp [Set.indicator_apply, hy, h2]
  rw [this, integral_add_left_eq_self (fun y => Set.indicator (Λ : Set V) g y) w]
end GlobalTheory.JR.WeilQuad.Fnf
