-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualUniq.fourB_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:42.323597+00:00
-- url     : https://prove2.me/submissions/3b3a46fb-dad2-4eef-9fe7-d0ed79d5d38f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
namespace GlobalTheory.JR.SelfDualUniq
theorem _root_.solution (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _
end GlobalTheory.JR.SelfDualUniq
