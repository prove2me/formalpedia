-- Prove2me | solution 1 for GlobalTheory.latticeMean_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:39.208842+00:00
-- url     : https://prove2.me/submissions/b337473e-0d6d-4bc5-ad8b-a0059c1b7222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_existsUnique_add_mem_latticeDomain
import Theorems.Thm_GlobalTheory_measurableSet_latticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_eq_latticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_eq

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
theorem _root_.solution {f : E → G} (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (w : E) :
    latticeMean L (fun x => f (x + w)) = latticeMean L f := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hD : IsAddFundamentalDomain L ((fun x => x + w) ⁻¹' latticeDomain L) μ := by
    refine IsAddFundamentalDomain.mk'
      ((measurable_add_const w) (measurableSet_latticeDomain L)).nullMeasurableSet fun x => ?_
    have := existsUnique_add_mem_latticeDomain L (x + w)
    simpa [Submodule.vadd_def, add_comm, add_left_comm, add_assoc] using this
  rw [latticeMean_eq L μ hD (f := fun x => f (x + w))
    (fun a ha x => by simpa [add_right_comm] using hf a ha (x + w)),
    latticeMean_eq_latticeDomain L μ]
  congr 1
  exact (measurePreserving_add_right μ w).setIntegral_preimage_emb
    (measurableEmbedding_addRight w) f _
end GlobalTheory
