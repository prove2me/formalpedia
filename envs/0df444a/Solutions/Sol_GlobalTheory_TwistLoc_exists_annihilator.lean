-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:45.687655+00:00
-- url     : https://prove2.me/submissions/4e9b106d-b5d7-4068-b0bc-f1528d34b3aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_GlobalTheory_TwistLoc_gs_cst
import Theorems.Thm_GlobalTheory_TwistLoc_isLocalization_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}
variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H
namespace GlobalTheory.TwistLoc
theorem _root_.solution {U : Y.Opens} (hU : IsCompact (U : Set Y)) (hU' : IsQuasiSeparated (U : Set Y))
    (a b : Γ(Y, U)) (hab : ∀ y, h y ∈ U → gs h y U a = gs h y U b) :
    ∃ t ∈ M, ∀ y ∈ U, gc π y t * gs (𝟙 Y) y U a = gc π y t * gs (𝟙 Y) y U b := by
  let := (h.app U).hom.toAlgebra
  have := isLocalization_app M H hU hU'
  have e : algebraMap Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) a = algebraMap Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) b := fn_ext fun y hy =>
    (gs_pull (𝟙 Y') h y U hy a).trans (Eq.trans (by rw [Category.id_comp]; exact hab y hy)
      (gs_pull (𝟙 Y') h y U hy b).symm)
  obtain ⟨⟨_, t, ht, rfl⟩, e'⟩ := IsLocalization.exists_of_eq (M := M.map (cst π U).hom) e
  refine ⟨t, ht, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 Y) y U) e'
  rw [gs_mul _ y U hy, gs_mul _ y U hy] at e''
  have c := gs_cst π (𝟙 Y) y U hy t
  rw [Category.id_comp] at c
  rw [← c]; exact e''
end GlobalTheory.TwistLoc
