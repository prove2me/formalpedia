-- Prove2me | solution 1 for GlobalTheory.LocLift.section_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:48.531687+00:00
-- url     : https://prove2.me/submissions/78de9786-bc12-40a9-bbd9-354ab6ac7f4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_LocLift_hom_nsmul


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
theorem _root_.solution {La : Type} [AddCommGroup La] {η' : La → (𝟙_ (Over X) ⟶ G)} (h : ∀ a c, η' (a + c) = η' a * η' c)
    {n : ℕ} {a : La} (hn : η' (n • a) = 1) (T : Over X) : (toUnit T ≫ η' a) ^ n = 1 := by
  rw [← hom_nsmul (e := fun a => toUnit T ≫ η' a) (fun a c => by rw [h, MonObj.comp_mul]), hn, MonObj.comp_one]
end GlobalTheory.LocLift
