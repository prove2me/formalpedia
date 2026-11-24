-- Prove2me | solution 1 for GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:58.287714+00:00
-- url     : https://prove2.me/submissions/d63db6a1-21ca-40c4-9d52-9a8042ab8831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Theorems.Thm_GlobalTheory_JR_SelfDualUniq_selfDual_exists_unique_isTest


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  first | exact @GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | exact GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | (intros; apply GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest <;> assumption)
end _root_.GlobalTheory.T
