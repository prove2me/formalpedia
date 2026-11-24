-- Prove2me | solution 1 for GlobalTheory.linearIndependent_real_of_int_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:10.284687+00:00
-- url     : https://prove2.me/submissions/bd1ec7e0-dd0e-4ddf-a76a-8121dbac48af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by
  have hle : span ℤ (Set.range v) ≤ L := span_le.2 (Set.range_subset_iff.2 hv)
  have hd : DiscreteTopology (span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion hle)
      (continuous_inclusion hle) (Set.inclusion_injective hle)
  rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
  rw [Real.finrank_eq_int_finrank_of_discrete hd, hli]
end GlobalTheory
