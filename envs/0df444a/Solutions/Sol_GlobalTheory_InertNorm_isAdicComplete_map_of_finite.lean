-- Prove2me | solution 1 for GlobalTheory.InertNorm.isAdicComplete_map_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:48.840036+00:00
-- url     : https://prove2.me/submissions/82c493e7-91a2-475c-ba67-02511efa07d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselianStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isPrecomplete_finite_module


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.InertNorm
namespace GlobalTheory.InertNorm
theorem _root_.solution {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsHausdorff I R := IsHausdorff.of_le_jacobson I R (IsAdicComplete.le_jacobson_bot I)
  have : IsPrecomplete I R := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I R
  exact ⟨⟩
end GlobalTheory.InertNorm
