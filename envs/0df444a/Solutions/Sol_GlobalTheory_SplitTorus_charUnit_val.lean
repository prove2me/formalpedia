-- Prove2me | solution 1 for GlobalTheory.SplitTorus.charUnit_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:23.062856+00:00
-- url     : https://prove2.me/submissions/c3573531-0e21-4eb1-92bb-d4b15675faec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  {T T' : Over S}
namespace GlobalTheory.SplitTorus
theorem _root_.solution (a : X) : (charUnit S X a).val = chi X a := by
  have h1 : chi (S := S) X a = (torusFst S X).appTop.hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (single a 1)) := by
    rw [chi, coord, Over.id_left, Category.id_comp]; rfl
  have h2 : (charUnit S X a).val = ((torusFst S X).appLE ⊤ ⊤ (fun _ _ => trivial)).hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (single a 1)) := by
    simp [charUnit, res, pullU, Scheme.Hom.appLE, AddMonoidAlgebra.of_apply]
    rfl
  rw [h1, h2, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
end GlobalTheory.SplitTorus
