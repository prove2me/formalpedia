-- Prove2me | solution 1 for GlobalTheory.LinDescent.FunctionsAreInvariants.unit_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:08.455276+00:00
-- url     : https://prove2.me/submissions/e1cdab7f-1b2c-47f2-a013-71167e00f0ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
namespace FunctionsAreInvariants
theorem _root_.solution (h : FunctionsAreInvariants t π) {V : Y.Opens}
    {a b : Γ(Y, V)ˣ} (e : ∀ x, π x ∈ V → gm (𝟙 X ≫ π) x V a = gm (𝟙 X ≫ π) x V b) : a = b := by
  refine Units.ext ((h V).1 (fn_ext fun x hx => ?_))
  rw [gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx,
    gs_unit (𝟙 X ≫ π) x V hx, e x hx]
end FunctionsAreInvariants
end GlobalTheory.LinDescent
