-- Prove2me | solution 1 for GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:46.383518+00:00
-- url     : https://prove2.me/submissions/b7e4709f-ea67-4b91-a3f4-020cd17d96f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Theorems.Thm_GlobalTheory_JR_selfDual_iff_lattice_volume_and_plancherel


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | exact GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | (intros; apply GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel <;> assumption)
end _root_.GlobalTheory.T
