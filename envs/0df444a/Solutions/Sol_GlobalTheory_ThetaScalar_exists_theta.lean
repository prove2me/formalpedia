-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:10.506328+00:00
-- url     : https://prove2.me/submissions/8e5d2325-1089-4b8b-8a98-66dd0d5239e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_theta_of_weilIs
import Theorems.Thm_GlobalTheory_ThetaScalar_opens_eq_top

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
variable {F : Type} [Field F] [IsAlgClosed F]
omit [IsAlgClosed F]
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hW : WeilSt) (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)
    (d : baseOver (Spec (CommRingCat.of F)) ⟶ P.A) (hd : d ^ k = 1) :
    ∃ θ : ThetaGrp P.A P.L k (baseOver (Spec (CommRingCat.of F))), θ.pt = d :=
  exists_theta_of_weilIs P.isLB (T := baseOver (Spec (CommRingCat.of F))) (IsLocalRing.closedPoint F)
    (opens_eq_top (𝟙 _) _) ((hW _ P k _).2.2.1 d hd)
end GlobalTheory.ThetaScalar
