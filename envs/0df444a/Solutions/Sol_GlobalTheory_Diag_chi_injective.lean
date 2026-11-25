-- Prove2me | solution 1 for GlobalTheory.Diag.chi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:03.144865+00:00
-- url     : https://prove2.me/submissions/6746b31e-e943-45cd-939c-cefd6e298dbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_cr_iso_bij


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
namespace GlobalTheory.Diag
theorem _root_.solution [Nonempty S] : Function.Injective (chi (S := S) X) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  intro a b hab
  let K := S.residueField s
  let p : Spec K ⟶ S := S.fromSpecResidueField s
  let φ : torusRing ZU X ⟶ CommRingCat.of (AddMonoidAlgebra K X) :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X
      ((Int.castRingHom K).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))
  let T : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) ≫ p)
  let t : T ⟶ splitTorus S X := ofCoord T (φ ≫ (Scheme.ΓSpecIso _).inv)
  have h1 : ∀ x, (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (chi X x) :=
    fun x => by rw [← Category.comp_id t, coord_comp, Category.comp_id]; rfl
  have h2 := (h1 a).trans ((congrArg _ hab).trans (h1 b).symm)
  rw [coord_ofCoord] at h2
  have h3 : φ.hom (AddMonoidAlgebra.single a 1) = φ.hom (AddMonoidAlgebra.single b 1) :=
    (cr_iso_bij (Scheme.ΓSpecIso (.of (AddMonoidAlgebra K X))).symm).1 h2
  simp only [φ, CommRingCat.hom_ofHom, AddMonoidAlgebra.mapRingHom_single, map_one] at h3
  exact AddMonoidAlgebra.single_left_injective one_ne_zero h3
end GlobalTheory.Diag
