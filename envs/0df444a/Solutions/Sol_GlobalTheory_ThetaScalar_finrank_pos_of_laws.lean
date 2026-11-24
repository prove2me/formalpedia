-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.finrank_pos_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:37.486323+00:00
-- url     : https://prove2.me/submissions/6aa31fbb-4720-4433-bb75-b9a6526b6663

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios

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
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hH : GlobalSectionsRankAlgClosed) (P : PolAV (Spec (CommRingCat.of F))) {k : ℕ} (hk : (k : F) ≠ 0) :
    0 < Module.finrank Γ((baseOver (Spec (CommRingCat.of F))).left, ⊤)
      (SecM P.A P.L (k : ℕ) (baseOver (Spec (CommRingCat.of F)))) := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun e => hk (by rw [e, Nat.cast_zero])
  rw [hH F P k hk1]
  exact Nat.pow_pos hk1
end GlobalTheory.ThetaScalar
