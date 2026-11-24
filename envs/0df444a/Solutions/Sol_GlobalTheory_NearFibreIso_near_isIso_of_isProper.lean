-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.near_isIso_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:04.450792+00:00
-- url     : https://prove2.me/submissions/6131522b-fbc4-43b6-9f01-e85cc9472d1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_NearFibreIso_Near_of_pullback
import Theorems.Thm_GlobalTheory_NearFibreIso_isIso_fibre_of_pullback
import Theorems.Thm_GlobalTheory_NearFibreIso_near_isFinite
import Theorems.Thm_GlobalTheory_NearFibreIso_near_isClosedImmersion
import Theorems.Thm_GlobalTheory_NearFibreIso_near_isIso

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
theorem _root_.solution [IsProper f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, hg, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := hg
  have : IsFinite f' := hQ
  have : IsIso (pullback.snd f' (pullback.fst (g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback s f _ H
  have hy : RingHom.ker (algebraMap R K) = ((g ≫ s) y).asIdeal := by simpa using hx
  obtain ⟨T₂, T₂', g₂, g₂', f₂, H₂, hg₂, ⟨y₂, rfl⟩, hQ₂⟩ := near_isClosedImmersion (g ≫ s) f' K y hy
  have := hg₂
  have : IsClosedImmersion f₂ := hQ₂
  have : IsIso (pullback.snd f₂ (pullback.fst (g₂ ≫ g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback (g ≫ s) f' _ H₂
  have : IsLocallyNoetherian T₂ := isLocallyNoetherian_of_isOpenImmersion (g₂ ≫ g)
  have : IsOpenImmersion g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hg
  have : IsOpenImmersion g₂' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H₂ hg₂
  have : Flat (f₂ ≫ g₂ ≫ g ≫ s) := by
    rw [reassoc_of% H₂.w, reassoc_of% H.w]
    infer_instance
  have hy₂ : RingHom.ker (algebraMap R K) = ((g₂ ≫ g ≫ s) y₂).asIdeal := by simpa using hy
  exact Near.of_pullback f H (Near.of_pullback f' H₂ (near_isIso (g₂ ≫ g ≫ s) f₂ K y₂ hy₂))
end GlobalTheory.NearFibreIso
