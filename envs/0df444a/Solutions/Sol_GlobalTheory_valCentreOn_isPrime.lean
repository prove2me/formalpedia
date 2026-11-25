-- Prove2me | solution 1 for GlobalTheory.valCentreOn_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:55.938313+00:00
-- url     : https://prove2.me/submissions/66654ab7-c61d-4aab-bf9c-c804db5709a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
import Theorems.Thm_GlobalTheory_mem_valCentreOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))
end GlobalTheory
