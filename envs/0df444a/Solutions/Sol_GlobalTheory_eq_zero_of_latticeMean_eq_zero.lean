-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_latticeMean_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:02.234541+00:00
-- url     : https://prove2.me/submissions/13514b82-4bf2-44ed-a27c-3accdbf96c59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_latticeProb_eq
import Theorems.Thm_GlobalTheory_integrable_latticeProb

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
theorem _root_.solution {f : E → ℝ} (hc : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (h : latticeMean L f = 0) : f = 0 := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [latticeMean_eq_integral, integral_eq_zero_iff_of_nonneg h0 (integrable_latticeProb L hc),
    latticeProb_eq L μ] at h
  have h1 : f =ᵐ[μ.restrict (latticeDomain L)] 0 :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)).1 h
  have hm : MeasurableSet {x | f x ≠ 0} :=
    (isOpen_ne_fun hc continuous_const).measurableSet
  have h2 : μ {x | f x ≠ 0} = 0 := by
    refine (isAddFundamentalDomain_latticeDomain L μ).measure_zero_of_invariant _ ?_ ?_
    · rintro ⟨a, ha⟩
      ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have := hf (-a) (L.neg_mem ha) x
      simp only [Submodule.vadd_def, Set.mem_setOf_eq, vadd_eq_add, NegMemClass.coe_neg]
      rw [add_comm, this]
    · rw [← Measure.restrict_apply hm]
      exact h1
  exact (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 h2
end GlobalTheory
