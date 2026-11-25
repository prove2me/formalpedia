-- Prove2me | solution 1 for GlobalTheory.FieldChange.pullB_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:47.183422+00:00
-- url     : https://prove2.me/submissions/6cfbd804-22af-4b15-8b37-ef52f3896801

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChange
import Theorems.Thm_GlobalTheory_FieldChange_sval_extend
import Theorems.Thm_GlobalTheory_FieldChange_fam_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
open GlobalTheory.FieldChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldChange
theorem _root_.solution {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α} {s : Raw D F k} (H : PullB D F φ k f s)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J :=
  sval_extend D.P.isLB _ (fam_comp D φ α) (s α) (f α) (H α) r z J hJ
end GlobalTheory.FieldChange
