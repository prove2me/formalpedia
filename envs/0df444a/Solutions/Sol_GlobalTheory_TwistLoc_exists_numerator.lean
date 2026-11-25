-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_numerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:03.883308+00:00
-- url     : https://prove2.me/submissions/879b9294-fa10-4cf3-aeaa-367bd8856c01

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
theorem _root_.solution {U : Y.Opens} (hU : IsAffineOpen U) (x : Γ(Y', h ⁻¹ᵁ U)) :
    ∃ t ∈ M, ∃ a : Γ(Y, U), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), h (r z) ∈ U →
      gs (r ≫ h) z U a = gc (r ≫ h ≫ π) z t * gs r z _ x := by
  let := (h.app U).hom.toAlgebra
  have := isLocalization_app M H hU.isCompact hU.isQuasiSeparated
  obtain ⟨⟨a, _, t, ht, rfl⟩, e⟩ := IsLocalization.surj (M.map (cst π U).hom) x
  refine ⟨t, ht, a, fun Z r z hz => ?_⟩
  have e' : (h.app U).hom a = x * (h.app U).hom ((cst π U).hom t) := e.symm
  rw [← gs_pull r h z U hz, e', gs_mul r z _ hz, gs_pull r h z U hz, gs_cst π (r ≫ h) z U hz, Category.assoc, mul_comm]
end GlobalTheory.TwistLoc
