-- Prove2me | solution 1 for GlobalTheory.TorsionPres.isUnit_of_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:18.456397+00:00
-- url     : https://prove2.me/submissions/6be9c107-8e66-4d56-bb7b-4980307fd76c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroup
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
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
    (eS : S →ₐ[O] O) (he : ∀ b, eS (algebraMap B S b) = e b) (s : S) (hs : IsUnit (eS s)) :
    IsUnit s := by
  obtain ⟨⟨b, t⟩, h⟩ :=
    IsLocalization.surj ((IsLocalRing.maximalIdeal O).comap e).primeCompl s
  have ht : IsUnit (e t) := IsLocalRing.notMem_maximalIdeal.mp t.2
  have hb : IsUnit (e b) := by
    have := congrArg eS h
    simp only [map_mul, he] at this
    rw [← this]
    exact hs.mul ht
  have hb' : b ∈ ((IsLocalRing.maximalIdeal O).comap e).primeCompl :=
    IsLocalRing.notMem_maximalIdeal.mpr hb
  have := IsLocalization.map_units S (⟨b, hb'⟩ : ((IsLocalRing.maximalIdeal O).comap e).primeCompl)
  exact isUnit_of_mul_isUnit_left (h ▸ this)
end GlobalTheory.TorsionPres
