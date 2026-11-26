-- Prove2me | solution 1 for Malliavin.range_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:04.700601+00:00
-- url     : https://prove2.me/submissions/0fe9d461-d704-4a4a-bd8c-1b1369f1be64

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) :
    LinearMap.range (wienerIntegral hB).toLinearMap = firstChaos hB := by
  apply le_antisymm
  · -- `J₁ f` is a limit of `J₁ (stepToLp v) = stepToRandom v ∈ span {B t}`
    rintro _ ⟨f, rfl⟩
    refine denseRange_stepToLp.induction_on f ?_ ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (wienerIntegral hB).continuous
    · intro v
      rw [ContinuousLinearMap.coe_coe, wienerIntegral_stepToLp]
      apply Submodule.le_topologicalClosure
      unfold stepToRandom
      rw [Finsupp.linearCombination_apply]
      exact Submodule.finsuppSum_mem _ _ _ _ fun t _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · -- the range is closed (isometry from a complete space) and contains every `B t`
    have hclosed : IsClosed (LinearMap.range (wienerIntegral hB).toLinearMap : Set (RandomL2 P)) :=
      (wienerIntegralₗᵢ hB).isometry.isClosedEmbedding.isClosed_range
    refine Submodule.topologicalClosure_minimal _ ?_ hclosed
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨intervalIndicator t, wienerIntegral_intervalIndicator hB t⟩
end Malliavin
