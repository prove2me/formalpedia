-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:08.540748+00:00
-- url     : https://prove2.me/submissions/76e38a8d-492f-4b8a-921b-f9341ac29063

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_exists_selfDual_of_dual_subgroups
import Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtMeas
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  obtain ⟨_, _, _, _, -⟩ := top_facts F V
  obtain ⟨hc, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  refine GlobalTheory.JR.exists_selfDual_of_dual_subgroups V (fun x y => ψ (β x y)) hc (fun x y => by rw [hs.eq]) (fun x x' y => ?_)
    (fun y => by simp) hl
  simp [AddChar.map_add_eq_mul]
end GlobalTheory.JR.EtMeas
