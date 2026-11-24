-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.regauge_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:40:59.437939+00:00
-- url     : https://prove2.me/submissions/0e86d472-45bc-4727-82a8-16fb6d4ecd74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
import Theorems.Thm_GlobalTheory_EpsCocycle_res_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section
namespace GlobalTheory.EpsCocycle
theorem _root_.solution {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB where
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group
end GlobalTheory.EpsCocycle
