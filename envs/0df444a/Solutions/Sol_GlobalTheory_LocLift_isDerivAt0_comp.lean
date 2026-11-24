-- Prove2me | solution 1 for GlobalTheory.LocLift.isDerivAt0_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:46:57.85383+00:00
-- url     : https://prove2.me/submissions/d99f5218-230c-497a-a4b9-8da3dda9097e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
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
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (h z)) w v ↔ IsDerivAt0 e (h w) v := by
  have key : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (h z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (h w) := fun U f => by
    have := h.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this w
  simp only [IsDerivAt0, key, map_zero]
end GlobalTheory.LocLift
