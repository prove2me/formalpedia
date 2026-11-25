-- Prove2me | solution 1 for GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:45.438049+00:00
-- url     : https://prove2.me/submissions/af007a56-e6b5-4820-b80c-407844d78b75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrIntegralClosureFiniteFractionRi
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrIntegralClosureFiniteFractionRiStatement
import Theorems.Thm_GlobalTheory_exists_complete_dvr_of_finite_fractionRing_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'), σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  first | exact @GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | exact GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | (intros; apply GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom <;> assumption)
end _root_.GlobalTheory.T
