-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:01.846901+00:00
-- url     : https://prove2.me/submissions/353bb9ca-8035-41d7-8bd5-8e30459bc284

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_lTensor_iotaQ_injective_of_retract
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact lTensor_iotaQ_injective_of_retract F (TrivSqZeroExt.inrHom R M) h (TrivSqZeroExt.sndHom R M)
    (LinearMap.ext fun m => by simp)
end GlobalTheory.CompanionTheory.WedgeOf
