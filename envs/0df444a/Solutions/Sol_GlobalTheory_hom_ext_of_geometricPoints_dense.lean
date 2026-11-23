-- Prove2me | solution 1 for GlobalTheory.hom_ext_of_geometricPoints_dense
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:42.403949+00:00
-- url     : https://prove2.me/submissions/da9a0173-3040-4e8c-a132-65b666b9d41f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y S : Scheme.{0}} [IsReduced X] (t : Y ⟶ S)
    [IsSeparated t] (f g : X ⟶ Y) (h : f ≫ t = g ≫ t) (D : Set X) (hD : Dense D)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.range x ⊆ D →
      x ≫ f = x ≫ g) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated t h (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨Dense.mono (fun x hx ↦ ?_) hD⟩
  let K := AlgebraicClosure (X.residueField x)
  let y : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
  have hy : ∀ p, y p = x := fun p ↦ Scheme.fromSpecResidueField_apply x _
  have hxy : y ≫ f = y ≫ g := H K y (by rintro _ ⟨p, rfl⟩; rwa [hy])
  have p : Sp K := IsLocalRing.closedPoint K
  refine ⟨equalizer.lift y hxy p, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, hy]
end GlobalTheory
