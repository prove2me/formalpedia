-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.psiVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:46.992751+00:00
-- url     : https://prove2.me/submissions/6f1e5aca-515f-433c-af98-99937006a539

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_IsPsiCoord_unique
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_psiCoord_spec

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
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
variable [IsLocalRing R] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal R Γ)
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution {D : DegPre R} {χ : D.X} {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    psiVal v D χ = v.toFun x := by
  obtain ⟨u, hu⟩ := (psiCoord_spec D χ).unique hx
  rw [psiVal, hu, v.map_mul, v.map_unit, zero_add]
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
