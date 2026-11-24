-- Prove2me | solution 1 for GlobalTheory.latContMap_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:40.723635+00:00
-- url     : https://prove2.me/submissions/64f222f6-d7fd-4989-9d64-c7aa9c70b391

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous
import Theorems.Thm_GlobalTheory_latContMap_apply

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E) (n : J → ℤ) :
    latContMap (fun i => p (e i)) (fun i => (n i : ℝ)) = p (e.equivFun.symm n) := by
  rw [latContMap_apply, Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, Int.cast_smul_eq_zsmul]
end GlobalTheory
