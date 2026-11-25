-- Prove2me | solution 1 for GlobalTheory.SecPow.exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:27.748221+00:00
-- url     : https://prove2.me/submissions/e65deede-8954-4595-88a9-a74838efc2f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection
import Theorems.Thm_GlobalTheory_SecPow_add_pow_succ_of_mul_self
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}
namespace GlobalTheory.SecPow
theorem _root_.solution {W O : X.Opens} (hW : IsCompact (W : Set X)) (hO : O ≤ W) (x y : Γ(X, W))
    (hsq : (y - x) * (y - x) = 0) (hx : X.basicOpen x ≤ O) (h : rs X hO x = rs X hO y) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → x ^ l = y ^ l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x ^ m * (y - x) = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW _ _ ?_
    have := congrArg (rs X hx) h
    rw [rs_rs, rs_rs] at this
    change rs X (hx.trans hO) (y - x) = 0
    rw [map_sub, this, sub_self]
  refine ⟨m + 1, fun l hl => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, l = (j + m) + 1 := ⟨l - (m + 1), by omega⟩
  have e := add_pow_succ_of_mul_self x (y - x) hsq (j + m)
  rw [add_sub_cancel, pow_add x j m, _root_.mul_assoc, hm] at e
  simpa using e.symm
end GlobalTheory.SecPow
