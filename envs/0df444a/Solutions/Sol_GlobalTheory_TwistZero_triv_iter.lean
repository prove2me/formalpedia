-- Prove2me | solution 1 for GlobalTheory.TwistZero.triv_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:13.923896+00:00
-- url     : https://prove2.me/submissions/a4dab71e-7e91-4ab5-81ae-c776eb0513fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_GlobalTheory_TwistZero_Triv_mul
import Theorems.Thm_GlobalTheory_TwistZero_Triv_congr
import Theorems.Thm_GlobalTheory_TwistZero_triv_square
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero
variable {k : Type} [Field k]
namespace GlobalTheory.TwistZero
theorem _root_.solution (hsq : SquareSt) (P : PolAV (Sp k)) (b : baseOver (Sp k) ⟶ P.A) :
    ∀ n : ℕ, Triv P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Sp k)) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)]
  | 0 => by
    refine Triv.congr P.isLB (formEq_of_add fun U _ hh => ?_) (triv_square hsq P b b)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine Triv.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((solution hsq P b n).mul (triv_square hsq P (b ^ (n + 2)) b))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module
end GlobalTheory.TwistZero
