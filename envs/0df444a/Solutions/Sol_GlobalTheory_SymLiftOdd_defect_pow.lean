-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.defect_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:00:03.269893+00:00
-- url     : https://prove2.me/submissions/bfb11cf4-543a-4f7e-a84e-fbbe7c8c7d15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution {G U : Type} [CommGroup G] [CommGroup U] (f n : G → U) (X : G) (k : ℕ) (hX : X ^ k = 1)
    (α β : U) (hα : ∀ m, f (X⁻¹ * m) * n m * (f m⁻¹ * (n (X⁻¹ * m))⁻¹) = α)
    (hβ : ∏ j ∈ Finset.range k, f (X ^ j) = β) : α ^ k = β ^ 2 := by
  have h1 : ∏ j ∈ Finset.range k, f (X ^ (j + 1))⁻¹ = β := by
    rw [← hβ, ← Finset.prod_range_reflect (fun j => f (X ^ j)) k]
    refine Finset.prod_congr rfl fun j hj => congrArg f ?_
    have hj' := Finset.mem_range.1 hj
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 1 + (k - 1 - j) = k by omega, hX]
  have h2 : ∏ j ∈ Finset.range k, (n (X ^ (j + 1)) / n (X ^ j)) = 1 := by
    rw [Finset.prod_range_div (fun j => n (X ^ j)) k, hX, pow_zero, div_self']
  have h3 : ∀ j ∈ Finset.range k, α = f (X ^ j) * f (X ^ (j + 1))⁻¹ * (n (X ^ (j + 1)) / n (X ^ j)) := by
    intro j _
    rw [← hα (X ^ (j + 1)), pow_succ' X j, inv_mul_cancel_left, div_eq_mul_inv]
    ac_rfl
  calc α ^ k = ∏ _j ∈ Finset.range k, α := by rw [Finset.prod_const, Finset.card_range]
    _ = β ^ 2 := by
      rw [Finset.prod_congr rfl h3, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hβ, h1, h2, _root_.mul_one, sq]
end GlobalTheory.SymLiftOdd
