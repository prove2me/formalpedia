-- Prove2me | solution 1 for GlobalTheory.mem_valCentreOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:23.473417+00:00
-- url     : https://prove2.me/submissions/3f110126-cc3f-4016-8eb7-24fc7a72b3f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation

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
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl
end GlobalTheory
