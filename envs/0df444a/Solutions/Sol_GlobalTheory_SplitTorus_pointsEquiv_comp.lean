-- Prove2me | solution 1 for GlobalTheory.SplitTorus.pointsEquiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:42.715463+00:00
-- url     : https://prove2.me/submissions/9ff72875-d954-4a3e-859d-8e85c87cb148

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
theorem _root_.solution (h : T' ⟶ T) (g : T ⟶ splitTorus S X) :
    pointsEquiv T' X (h ≫ g) =
      (MonoidHom.toAdditive (Units.map h.left.appTop.hom.toMonoidHom)).comp (pointsEquiv T X g) := by
  ext a
  exact val_comp h g a
end GlobalTheory.SplitTorus
