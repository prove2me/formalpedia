-- Prove2me | solution 1 for GlobalTheory.T.factor_through_generic_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:52.322034+00:00
-- url     : https://prove2.me/submissions/462a4519-1b71-4cb9-89d3-b4d4d07a3cf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FactorThroughGenericFiber
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FactorThroughGenericFiberStatement
import Theorems.Thm_GlobalTheory_factor_through_fractionField_of_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0}) (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) → ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  first | exact @GlobalTheory.factor_through_fractionField_of_range | exact GlobalTheory.factor_through_fractionField_of_range | (intros; apply GlobalTheory.factor_through_fractionField_of_range <;> assumption)
end _root_.GlobalTheory.T
