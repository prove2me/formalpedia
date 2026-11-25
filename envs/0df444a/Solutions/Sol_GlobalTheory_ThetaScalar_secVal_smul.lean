-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.secVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:30.28112+00:00
-- url     : https://prove2.me/submissions/ea04de59-756a-40eb-977e-2d137a3dfbae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_secVal_of_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (c : Γ(T.left, ⊤)) (f : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    secVal (SecM.toSec A (c • f)) r z J = gs (r ≫ (fst T A).left) z ⊤ c * secVal (SecM.toSec A f) r z J :=
  secVal_of_eq_mul (fun _ => rfl) r z hJ
end GlobalTheory.ThetaScalar
