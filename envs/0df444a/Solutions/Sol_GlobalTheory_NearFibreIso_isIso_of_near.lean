-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.isIso_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:46.790796+00:00
-- url     : https://prove2.me/submissions/c28b6a4f-4db0-4bd3-91ed-43c12f530860

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
variable (K : Type) [Field K] [Algebra R K]
namespace GlobalTheory.NearFibreIso
theorem _root_.solution {S : Scheme.{0}} (t : S ⟶ X)
    (h : ∀ y : S, Near f (MorphismProperty.isomorphisms _) (t y)) : IsIso (pullback.snd f t) := by
  choose T T' g g' f' H hg hx hQ using h
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun y => t ⁻¹ᵁ (g y).opensRange) ?_ fun y => ?_
  · refine eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    simpa using hx z
  · have := hg y
    have : IsIso (f' y) := hQ y
    have hle : Set.range (Scheme.Opens.ι (t ⁻¹ᵁ (g y).opensRange) ≫ t) ⊆ Set.range (g y) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    have hu := IsOpenImmersion.lift_fac (g y) _ hle
    have big := (isPullback_morphismRestrict (pullback.snd f t) (t ⁻¹ᵁ (g y).opensRange)).paste_vert
      (IsPullback.of_hasPullback f t).flip
    rw [← hu] at big
    rw [MorphismProperty.isomorphisms.iff]
    exact (big.of_bot' (H y)).isIso_fst_of_isIso
end GlobalTheory.NearFibreIso
