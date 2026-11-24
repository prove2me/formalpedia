-- Prove2me | solution 1 for GlobalTheory.T.first_cohomology_inclusion_tensor_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:19.448041+00:00
-- url     : https://prove2.me/submissions/e6ed686f-5be2-4603-ac12-dee2d1e24e5c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjectiveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_iotaQ_lTensor_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | exact GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective <;> assumption)
end _root_.GlobalTheory.T
