-- Prove2me | solution 1 for GlobalTheory.end_eq_zero_of_quad_const_on_cosets_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:29.28681+00:00
-- url     : https://prove2.me/submissions/f0359315-59bd-4072-87b8-163080c8b77e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Theorems.Thm_GlobalTheory_end_eq_zero_of_quad_const_on_cosets
import Theorems.Thm_GlobalTheory_isUnit_two_zmod_pow
import Theorems.Thm_GlobalTheory_isNilpotent_natCast_zmod_pow
import Theorems.Thm_GlobalTheory_meets_cosets_nsmul_of_meets_cosets_torsion
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Function
open GlobalTheory
variable {n k : ℕ}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set (ι → ZMod (n ^ k)))
    (hT : (∀ x, ∃ t ∈ T, ∃ a, x = t + n • a) ∨ (2 ≤ k ∧ ∀ x, ∃ t ∈ T, n • (x - t) = 0))
    (c : ZMod (n ^ k)) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have hT' : ∀ x, ∃ t ∈ T, ∃ a, x = t + n • a :=
    hT.elim id fun h => meets_cosets_nsmul_of_meets_cosets_torsion hn.pos.ne' h.1 T h.2
  refine end_eq_zero_of_quad_const_on_cosets (isUnit_two_zmod_pow hn k)
    (isNilpotent_natCast_zmod_pow n k) ω hω S hS u q hq T (fun x => ?_) c hc
  simpa only [Nat.cast_smul_eq_nsmul] using hT' x
end GlobalTheory
