-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.form_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:29.746008+00:00
-- url     : https://prove2.me/submissions/5c54c107-5967-4633-a7ae-28da1f530f15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translPt
import Theorems.Thm_GlobalTheory_SymLiftOdd_translT_eq
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2

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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution {n : ℕ} {x : T ⟶ A} (hx : x ^ n = 1) (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U) :
    ∏ p, h (powφ A x n p) ^ powε k n p = 1 := by
  let g : ℕ → U := fun j => h ((fst T A ≫ x) ^ j * snd T A).left ^ (-k)
  have e : ∀ j : Fin n, ∏ b : Fin 2, h (powφ A x n (j, b)) ^ powε k n (j, b) = g (j + 1) / g j := fun j => by
    rw [Fin.prod_univ_two]
    show h (translT A (x ^ (j : ℕ)) ≫ snd T A).left ^ k * h (translT A (x ^ (j : ℕ)) ≫ translPt A x).left ^ (-k) = _
    rw [translT_eq, lift_snd, lift_translPt, comp_pow', ← _root_.mul_assoc, ← pow_succ', div_eq_mul_inv, mul_comm]
    simp only [g, zpow_neg, inv_inv]
  rw [Fintype.prod_prod_type, Finset.prod_congr rfl fun j _ => e j, ← Finset.prod_range (fun j => g (j + 1) / g j),
    Finset.prod_range_div]
  simp only [g]
  rw [← comp_pow', hx, MonObj.comp_one, pow_zero, div_self']
end GlobalTheory.SymLiftOdd
