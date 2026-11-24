-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.setIntegral_swap_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:46.576281+00:00
-- url     : https://prove2.me/submissions/9eb121e7-b3f3-48d7-b449-ea476baab957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss
namespace GlobalTheory.JR.ResidueGauss
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (S : Set X) (T : Set Y) (hS : μ S ≠ ⊤) (hT : ν T ≠ ⊤) (g : X → Y → ℂ)
    (hg : Continuous (Function.uncurry g)) (hb : ∀ x y, ‖g x y‖ ≤ 1) :
    ∫ x in S, ∫ y in T, g x y ∂ν ∂μ = ∫ y in T, ∫ x in S, g x y ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict T) := ⟨by simpa using hT.lt_top⟩
  apply integral_integral_swap
  exact Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun q => hb q.1 q.2)
end GlobalTheory.JR.ResidueGauss
