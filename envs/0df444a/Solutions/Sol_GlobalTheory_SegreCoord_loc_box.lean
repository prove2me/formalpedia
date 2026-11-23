-- Prove2me | solution 1 for GlobalTheory.SegreCoord.loc_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:58.495143+00:00
-- url     : https://prove2.me/submissions/0dd58341-60ab-4dcb-b960-fd424b6eb3cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {Y : Scheme.{0}} (p q : Y ⟶ X)
namespace GlobalTheory.SegreCoord
theorem _root_.solution {x : Sp T ⟶ Y} {v₁ v₂ : σ → T} (h₁ : Loc M th (x ≫ p) v₁) (h₂ : Loc M th (x ≫ q) v₂) :
    Loc (boxLB M p q) (boxTh th p q) x (fun i => v₁ i.1 * v₂ i.2) := fun y j hy => by
  obtain ⟨u₁, e₁⟩ := h₁ y (j 0) (LB.wchart_le M ![p, q] j 0 hy)
  obtain ⟨u₂, e₂⟩ := h₂ y (j 1) (LB.wchart_le M ![p, q] j 1 hy)
  refine ⟨u₁ * u₂, fun i => (gs_boxF p q _ _ j x y hy).trans ?_⟩
  rw [e₁, e₂, map_mul, Units.val_mul, mul_mul_mul_comm]
end GlobalTheory.SegreCoord
