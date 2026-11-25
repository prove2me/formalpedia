-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.Rep.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:16.645521+00:00
-- url     : https://prove2.me/submissions/8972f08d-e07d-4ad9-bbe0-10442a6906c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_mul
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}
namespace GlobalTheory.UT.PhiOrder
namespace Rep
theorem _root_.solution {V : ℕ → _} {W : ℕ → _} (h : ∀ j, Rep D (V j) (W j)) (n : ℕ) :
    Rep D (fun T x z J => ∏ j ∈ Finset.range n, V j T x z J) (fun U _ g => ∏ j ∈ Finset.range n, W j U g) := by
  induction n with
  | zero => exact Rep.one
  | succ n ih => simpa only [Finset.prod_range_succ] using ih.mul (h n)
end Rep
end GlobalTheory.UT.PhiOrder
