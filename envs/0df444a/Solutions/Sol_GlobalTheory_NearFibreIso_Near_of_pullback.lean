-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.Near.of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:41.661504+00:00
-- url     : https://prove2.me/submissions/e554e672-a197-4ec2-983c-127f099abd3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback

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
namespace GlobalTheory.NearFibreIso
namespace Near
theorem _root_.solution {Q : MorphismProperty Scheme.{0}} {T T' : Scheme.{0}} {g : T ⟶ X}
    {g' : T' ⟶ Y} {f' : T' ⟶ T} (H : IsPullback f' g' g f) [IsOpenImmersion g] {y : T}
    (h : Near f' Q y) : Near f Q (g y) := by
  obtain ⟨T₀, T₀', g₀, g₀', f₀, H₀, hg₀, ⟨z, rfl⟩, hQ⟩ := h
  have := hg₀
  refine ⟨T₀, T₀', g₀ ≫ g, g₀' ≫ g', f₀, H₀.paste_vert H, inferInstance, ⟨z, ?_⟩, hQ⟩
  simp
end Near
end GlobalTheory.NearFibreIso
