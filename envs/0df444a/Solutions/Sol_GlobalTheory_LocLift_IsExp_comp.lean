-- Prove2me | solution 1 for GlobalTheory.LocLift.IsExp.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:37.11807+00:00
-- url     : https://prove2.me/submissions/227fac59-e057-4acb-ac89-089b744afd24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_comp
import Theorems.Thm_GlobalTheory_LocLift_isDerivAt0_comp
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
namespace IsExp
theorem _root_.solution {y : Sp ℂ ⟶ X} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp y e)
    (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : IsExp y (fun z => e (h z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  refine ⟨fun z w => by simp only [map_add, h1], h2.comp h.surjective,
    isHolTo_comp h3 isOpen_univ h.differentiableOn (Set.mapsTo_univ _ _), fun w => ?_, fun v hv => ?_⟩
  · simpa only [isDerivAt0_comp (e := fun z => (e z).left)] using h4 (h w)
  · simp only [isDerivAt0_comp (e := fun z => (e z).left)]
    obtain ⟨w, hw, hu⟩ := h5 v (by simpa only [map_zero] using hv)
    exact ⟨h.symm w, by simpa using hw, fun w' hw' => by rw [← hu _ hw', h.symm_apply_apply]⟩
end IsExp
end GlobalTheory.LocLift
