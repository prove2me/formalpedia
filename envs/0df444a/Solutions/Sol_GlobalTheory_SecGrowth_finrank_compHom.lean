-- Prove2me | solution 1 for GlobalTheory.SecGrowth.finrank_compHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:28.234938+00:00
-- url     : https://prove2.me/submissions/f8bd8b7b-d22f-4553-b25a-cae8d3fb351c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V] :
    letI := Module.compHom V e.toRingHom
    Module.finrank K V = Module.finrank R V := by
  letI := Module.compHom V e.toRingHom
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv e (AddEquiv.refl V) e.bijective fun _ _ => rfl)
end GlobalTheory.SecGrowth
