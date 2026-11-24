-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:02.630807+00:00
-- url     : https://prove2.me/submissions/2035d391-424b-437e-87b8-8479a0267def

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
import Theorems.Thm_GlobalTheory_UT_PhiOrder_prod_wN

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
theorem _root_.solution (h : A → U) (x : A) (m k : ℕ) (hk : k = 2 * m + 1) :
    ((h (x ^ k * (x ^ k)⁻¹ * x ^ k) * (h (x ^ k * (x ^ k)⁻¹))⁻¹ * (h (x ^ k * x ^ k))⁻¹ * (h ((x ^ k)⁻¹ * x ^ k))⁻¹ *
        h (x ^ k) * h (x ^ k)⁻¹ * h (x ^ k) * (h 1)⁻¹ * (h (x ^ k)⁻¹ * (h (x ^ k))⁻¹)⁻¹) *
        ∏ j ∈ Finset.range (2 * k), wN h x j) ^ m * ((∏ j ∈ Finset.range k, wN h x j) ^ (k + 2 * m))⁻¹ =
      h x ^ ((k ^ 2 : ℕ) : ℤ) * h (x ^ k) ^ (-((1 : ℕ) : ℤ)) * h 1 ^ (((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)) := by
  have a₁ := prod_wN h x (2 * k) (k * (2 * k - 1)) (by push_cast; ring)
  have a₂ := prod_wN h x k (m * k) (by rw [hk]; push_cast; ring)
  rw [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_add, ← two_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, a₁, a₂]
  subst hk
  push_cast
  module
end GlobalTheory.UT.PhiOrder
