-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.prod_wN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:40.371853+00:00
-- url     : https://prove2.me/submissions/fb98623d-bc3a-483b-a653-12f1e4a2b68a

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
variable {A U : Type} [CommGroup A] [CommGroup U]
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (h : A → U) (x : A) (n : ℕ) (T : ℤ) (hT : 2 * T = n * (n - 1)) :
    Additive.ofMul (∏ j ∈ Finset.range n, wN h x j) = Additive.ofMul (h (x ^ n)) - T • Additive.ofMul (h (x ^ 2)) +
      (2 * T - n) • Additive.ofMul (h x) + (n - 1 - T) • Additive.ofMul (h 1) := by
  induction n generalizing T with
  | zero =>
    obtain rfl : T = 0 := by simpa using hT
    simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ofMul_mul, ih (T - n) (by push_cast at hT; linear_combination hT)]
    simp only [wN, ofMul_mul, ofMul_inv, ofMul_pow]
    push_cast
    module
end GlobalTheory.UT.PhiOrder
