-- Prove2me | solution 1 for GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:03.723909+00:00
-- url     : https://prove2.me/submissions/32a85990-f813-4983-8e64-7ee90d316319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement
import Theorems.Thm_GlobalTheory_OpenImmDim_topologicalKrullDim_eq_of_isOpenImmersion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  first | exact @GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | exact GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | (intros; apply GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion <;> assumption)
end _root_.GlobalTheory.T
