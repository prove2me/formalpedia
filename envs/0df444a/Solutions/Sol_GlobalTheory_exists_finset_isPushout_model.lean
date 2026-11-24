-- Prove2me | solution 1 for GlobalTheory.exists_finset_isPushout_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:43.873774+00:00
-- url     : https://prove2.me/submissions/3acdd0cc-54a0-4d95-859c-d411c486c83c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
      ∃ (A₀ : CommRingCat.{0}) (f : CommRingCat.of k ⟶ A₀) (g : A₀ ⟶ CommRingCat.of A),
        IsPushout f (CommRingCat.ofHom β) g (CommRingCat.ofHom (algebraMap K A)) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation K A
  refine ⟨P.finite_coeffs.toFinset, fun k _ β hs => ?_⟩
  letI : Algebra k K := β.toAlgebra
  letI : Algebra k A := ((algebraMap K A).comp β).toAlgebra
  haveI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : P.HasCoeffs k := ⟨fun x hx => hs (by simpa using hx)⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k K (P.ModelOfHasCoeffs k)).flip
  refine ⟨CommRingCat.of (P.ModelOfHasCoeffs k), CommRingCat.ofHom (algebraMap k _),
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫
      e.toRingEquiv.toCommRingCatIso.hom, ?_⟩
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · ext x
    exact e.commutes x
end GlobalTheory
