-- Prove2me | solution 1 for GlobalTheory.TorsionPres.exists_lift_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:31.905233+00:00
-- url     : https://prove2.me/submissions/1f89ad1a-c842-44b1-9d20-5571304d8c08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroup
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionPres
variable {O : Type} [CommRing O] [IsLocalRing O] {B : Type} [CommRing B] [Algebra O B]
namespace GlobalTheory.TorsionPres
theorem _root_.solution (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    {A : Type} [CommRing A] [Algebra O A] (h : B →ₐ[O] A)
    (hh : ∀ b, IsUnit (e b) → IsUnit (h b)) :
    ∃ φ : S →ₐ[O] A, ∀ b, φ (algebraMap B S b) = h b := by
  have hu : ∀ t : ((IsLocalRing.maximalIdeal O).comap e).primeCompl, IsUnit (h t) := fun t =>
    hh _ (IsLocalRing.notMem_maximalIdeal.mp t.2)
  exact ⟨IsLocalization.liftAlgHom (S := S) hu, fun b => by
    simp [IsLocalization.liftAlgHom_apply]⟩
end GlobalTheory.TorsionPres
