-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.cubN_eq_pot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:47.047357+00:00
-- url     : https://prove2.me/submissions/d4160ec1-518f-4744-a517-7a6a781091db

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
import Theorems.Thm_GlobalTheory_UT_PhiOrder_cub_eq_pot

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
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (h : IsCub θ) (b : A) (n a c x : ℕ) :
    Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = Additive.ofMul (pot θ b (a + c * n + x)) -
      Additive.ofMul (pot θ b (a + x)) - Additive.ofMul (pot θ b (a + c * n)) + Additive.ofMul (pot θ b a) -
      n • (Additive.ofMul (pot θ b (c + x)) - Additive.ofMul (pot θ b c) - Additive.ofMul (pot θ b x)) := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    rw [cubN, Finset.prod_range_succ, ofMul_mul, ← cubN, ih, ← pow_mul, ← pow_add, cub_eq_pot h, mul_add c n 1,
      _root_.mul_one, ← add_assoc a, succ_nsmul]
    abel
end GlobalTheory.UT.PhiOrder
