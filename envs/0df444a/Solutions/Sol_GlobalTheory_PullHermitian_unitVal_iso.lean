-- Prove2me | solution 1 for GlobalTheory.PullHermitian.unitVal_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:42.122904+00:00
-- url     : https://prove2.me/submissions/d9f14dfd-3ff2-45e3-9b0e-2d0a65befb3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.PullHermitian
theorem _root_.solution {M N : LB X} (w : LB.Iso N M) (hw : w.IsGen) (i i' : M.ι) (j j' : N.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ M.U i') (hj : ⊤ ≤ x ⁻¹ᵁ N.U j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ N.U j') :
    unitVal x (U := (LB.div M N).U (i, j)) (inf_of x hi hj) (w.s (i, j)) =
      unitVal x (inf_of x hi hi') (M.g i i') * (unitVal x (inf_of x hj hj') (N.g j j'))⁻¹ *
        unitVal x (U := (LB.div M N).U (i', j')) (inf_of x hi' hj') (w.s (i', j')) := by
  have h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M N).U (i, j) ⊓ (LB.div M N).U (i', j')) :=
    inf_of x (inf_of x hi hj) (inf_of x hi' hj')
  refine (unitVal_res x inf_le_left h _ _).symm.trans ?_
  refine (congrArg (unitVal x h) (hw (i, j) (i', j'))).trans ?_
  refine (map_mul (unitVal x h) _ _).trans ?_
  refine congrArg₂ (· * ·) ?_ (unitVal_res x inf_le_right h _ _)
  refine (map_mul (unitVal x h) _ _).trans ?_
  exact congrArg₂ (· * ·) (unitVal_res x _ h _ _)
    ((map_inv (unitVal x h) _).trans (congrArg (·⁻¹) (unitVal_res x _ h _ _)))
end GlobalTheory.PullHermitian
