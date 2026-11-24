-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.near_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:51.507862+00:00
-- url     : https://prove2.me/submissions/e75ab749-b95a-4809-9da2-d1a10f34f9a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_surjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_local_of_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
variable (K : Type) [Field K] [Algebra R K]
namespace GlobalTheory.NearFibreIso
theorem _root_.solution [hfin : IsFinite f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f @IsClosedImmersion x := by
  refine DenseFibreIso.local_of_ring s f @IsClosedImmersion K ?_ x hx
  intro A B _ _ _ _ _ _ j j' _ H _ hbij m
  have hf : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) H.flip hfin
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  obtain ⟨a, ha, hsurj⟩ := DenseFibreIso.exists_away_surjective (A ⊗[R] K) hbij.2 m
  exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ hsurj⟩
end GlobalTheory.NearFibreIso
