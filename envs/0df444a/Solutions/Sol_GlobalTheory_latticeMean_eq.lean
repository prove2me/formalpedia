-- Prove2me | solution 1 for GlobalTheory.latticeMean_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:52.570784+00:00
-- url     : https://prove2.me/submissions/4a298c28-d2ae-465c-8ec2-0670e39406c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_eq_latticeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {D : Set E} (hD : IsAddFundamentalDomain L D μ) {f : E → G}
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) :
    latticeMean L f = (ZLattice.covolume L μ)⁻¹ • ∫ x in D, f x ∂μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [latticeMean_eq_latticeDomain L μ,
    (isAddFundamentalDomain_latticeDomain L μ).setIntegral_eq hD]
  rintro ⟨a, ha⟩ x
  simpa [Submodule.vadd_def, add_comm] using hf a ha x
end GlobalTheory
