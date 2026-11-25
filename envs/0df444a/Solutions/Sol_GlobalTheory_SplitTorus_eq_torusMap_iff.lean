-- Prove2me | solution 1 for GlobalTheory.SplitTorus.eq_torusMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:26.456269+00:00
-- url     : https://prove2.me/submissions/f2c5c027-3917-4bc6-bfe9-e6029cfebf4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_appTop_chi

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
theorem _root_.solution (f : splitTorus S X ⟶ splitTorus S Y) (φ : Y →+ X) :
    f = torusMap S φ ↔ ∀ b, f.left.appTop.hom (chi Y b) = chi X (φ b) :=
  ⟨fun h b => h ▸ torusMap_appTop_chi φ b, fun h => hom_ext fun b => by rw [val_eq, h, val_torusMap]⟩
end GlobalTheory.SplitTorus
