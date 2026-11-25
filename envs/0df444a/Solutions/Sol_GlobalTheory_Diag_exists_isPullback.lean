-- Prove2me | solution 1 for GlobalTheory.Diag.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:48.329241+00:00
-- url     : https://prove2.me/submissions/82ec44a1-870a-4f1b-a309-29fa5f31ccf3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap

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
variable (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X]
attribute [local instance] intAlgebra
open scoped AlgebraMonoidAlgebra
variable {S R}
namespace GlobalTheory.Diag
theorem _root_.solution (g : S ⟶ Spec (.of R)) :
    ∃ a : (splitTorus S X).left ⟶ Spec (.of (AddMonoidAlgebra R X)),
      IsPullback a (splitTorus S X).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))) g := by
  have h := isPullback_groupRing R X
  refine ⟨h.lift (torusFst S X) ((splitTorus S X).hom ≫ g) (specULiftZIsTerminal.hom_ext _ _),
    IsPullback.of_right ?_ (h.lift_snd _ _ _) h⟩
  rw [h.lift_fst, show g ≫ toZ (Spec (.of R)) = toZ S from specULiftZIsTerminal.hom_ext _ _]
  exact isPullback_torusFst S X
end GlobalTheory.Diag
