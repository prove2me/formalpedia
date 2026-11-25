-- Prove2me | solution 1 for GlobalTheory.LocLift.lattice_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:53.137851+00:00
-- url     : https://prove2.me/submissions/5d652cca-f26a-4042-9260-041e44a216e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution {La : Type} [AddCommGroup La] {P : La →+ (Fin g → ℂ)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    {P' : La →+ (Fin g → ℂ)} (hP : ∀ x, h (P' x) = P x) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hd : DiscreteTopology P.range) : Submodule.span ℝ (Set.range P') = ⊤ ∧ DiscreteTopology P'.range := by
  constructor
  · have : Set.range P' = (h.symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]
      congr 1
      ext1 x
      exact h.eq_symm_apply.2 (hP x)
    rw [this, ← Submodule.map_span, hs, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · refine DiscreteTopology.of_continuous_injective (β := P.range)
      (f := fun z => ⟨h z, by obtain ⟨_, x, rfl⟩ := z; exact ⟨x, (hP x).symm⟩⟩) (by fun_prop) fun a b hab => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hab))
end GlobalTheory.LocLift
