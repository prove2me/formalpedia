-- Prove2me | solution 1 for GlobalTheory.T.group_action_haar_scaling_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:11.865004+00:00
-- url     : https://prove2.me/submissions/ba4b69ed-6845-4e59-93e2-77d22684352d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GroupActionHaarScalingContinuous
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GroupActionHaarScalingContinuousStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_ModulusAction_exists_continuous_modulus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V), (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) → (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) → ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | exact GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | (intros; apply GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus <;> assumption)
end _root_.GlobalTheory.T
