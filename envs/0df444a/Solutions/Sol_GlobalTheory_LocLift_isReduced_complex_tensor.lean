-- Prove2me | solution 1 for GlobalTheory.LocLift.isReduced_complex_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:25.089955+00:00
-- url     : https://prove2.me/submissions/4911e75d-1c8d-4c62-a620-900a1177a125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_LocLift_IsExp_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution (E : Type) [Field E] [NumberField E] : IsReduced (ℂ ⊗[ℤ] 𝓞 E) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : Algebra.FormallyUnramified ℤ E := Algebra.FormallyUnramified.comp ℤ ℚ E
  haveI : Algebra.EssFiniteType ℤ E := Algebra.EssFiniteType.comp ℤ ℚ E
  haveI : IsReduced (ℂ ⊗[ℤ] E) := Algebra.FormallyUnramified.isReduced_of_field ℂ (ℂ ⊗[ℤ] E)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ ℂ) (IsScalarTower.toAlgHom ℤ (𝓞 E) E)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj
end GlobalTheory.LocLift
