-- Prove2me | solution 1 for GlobalTheory.latticeMean_eq_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:13.672986+00:00
-- url     : https://prove2.me/submissions/98282b31-a026-41d6-b3c0-6cf0c3505d43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_comp_add
import Theorems.Thm_GlobalTheory_exists_forall_le_of_periodic

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
theorem _root_.solution (L' : Submodule ℤ E) [DiscreteTopology L'] [IsZLattice ℝ L']
    [CompleteSpace G] {f : E → G} (hc : Continuous f) (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x)
    (hf' : ∀ a ∈ L', ∀ x, f (x + a) = f x) : latticeMean L f = latticeMean L' f := by
  borelize E
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_of_periodic L hc.norm (fun a ha x => by rw [hf a ha x])
  have hi : Integrable (Function.uncurry fun x y : E => f (x + y))
      ((latticeProb L).prod (latticeProb L')) :=
    Integrable.of_bound (hc.comp continuous_add).aestronglyMeasurable ‖f x₀‖
      (ae_of_all _ fun p => hx₀ _)
  have h := integral_integral_swap hi
  simp only [← latticeMean_eq_integral] at h
  have h1 : ∀ x, latticeMean L' (fun y => f (x + y)) = latticeMean L' f := fun x => by
    simpa only [add_comm x] using latticeMean_comp_add L' hf' x
  simp only [h1, latticeMean_comp_add L hf, latticeMean_const] at h
  exact h.symm
end GlobalTheory
