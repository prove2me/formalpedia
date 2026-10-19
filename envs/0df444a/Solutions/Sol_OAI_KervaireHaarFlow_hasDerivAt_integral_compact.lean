-- Prove2me | solution 1 for OAI.KervaireHaarFlow.hasDerivAt_integral_compact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:52:39.985422+00:00
-- url     : https://prove2.me/submissions/91033b6b-c53d-4bc8-a12c-9e90a6c7eed6

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents

open OAI OAI.KervaireHaarFlow
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]
theorem solution {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) (∫ x, df t x ∂μ) t := by
  have hcf : ∀ u, Continuous (f u) := fun u => hf.comp (continuous_const.prodMk continuous_id)
  have hcd : ∀ u, Continuous (df u) := fun u => hd.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ (X := S))).exists_bound_of_continuousOn
    hd.continuousOn
  have hint : Integrable (f t) μ := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn (hcf t).continuousOn
    exact Integrable.of_bound (hcf t).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => hC x trivial))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.closedBall t 1)
    (Metric.closedBall_mem_nhds t one_pos)
    (Filter.Eventually.of_forall (fun u => (hcf u).aestronglyMeasurable)) hint
    (hcd t).aestronglyMeasurable (bound := fun _ => M)
    (Filter.Eventually.of_forall (fun x u hu => hM (u, x) ⟨hu, trivial⟩)) (integrable_const M)
    (Filter.Eventually.of_forall (fun x u _ => hfd u x))).2

