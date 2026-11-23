-- Prove2me | solution 1 for GlobalTheory.LocLift.linear_lift_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:38.73567+00:00
-- url     : https://prove2.me/submissions/9107a8cf-6058-4bff-b607-6850baa524aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_hom_sub_eq_one
import Theorems.Thm_GlobalTheory_LocLift_isDiscrete_of_norm
import Theorems.Thm_GlobalTheory_realLinear_eq_of_sub_mem_discrete


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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]
namespace GlobalTheory.LocLift
theorem _root_.solution {e : W → Q} (h : ∀ z w, e (z + w) = e z * e w) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {L L' : V →ₗ[ℂ] W} (hL : ∀ z, e (L z) = e (L' z)) : L = L' := by
  have := realLinear_eq_of_sub_mem_discrete (Γ := homKer h) (isDiscrete_of_norm hr fun z hz hn => hk z hn hz)
    (L := L.restrictScalars ℝ) (L' := L'.restrictScalars ℝ) fun x => (hom_sub_eq_one h).2 (hL x)
  ext z
  exact DFunLike.congr_fun this z
end GlobalTheory.LocLift
