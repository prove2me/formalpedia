-- Prove2me | solution 1 for GlobalTheory.end_eq_zero_of_twist_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:56.796649+00:00
-- url     : https://prove2.me/submissions/bf957b7b-ce39-422e-b529-6aaff2f72ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Theorems.Thm_GlobalTheory_end_eq_zero_of_quad_const_on_cosets_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
variable {n k : ℕ}
namespace GlobalTheory
theorem _root_.solution {ι K : Type*} [CommRing K] [IsDomain K] (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ k))
    (θ θ' : (ι → ZMod (n ^ k)) → K) (hθ : ∀ x, θ' x = ζ ^ (q x).val * θ x)
    (c : K) (hc : ∀ x, θ' x = c * θ x)
    (hT : (∀ x, ∃ t, θ t ≠ 0 ∧ ∃ a, x = t + n • a) ∨
      (2 ≤ k ∧ ∀ x, ∃ t, θ t ≠ 0 ∧ n • (x - t) = 0)) : S = 0 := by
  haveI : NeZero (n ^ k) := ⟨pow_ne_zero _ hn.pos.ne'⟩
  have h1 : ∀ t, θ t ≠ 0 → ζ ^ (q t).val = c := fun t ht =>
    mul_right_cancel₀ ht ((hθ t).symm.trans (hc t))
  obtain ⟨t₀, ht₀⟩ : ∃ t, θ t ≠ 0 :=
    hT.elim (fun h => (h 0).imp fun _ h => h.1) fun h => (h.2 0).imp fun _ h => h.1
  refine end_eq_zero_of_quad_const_on_cosets_zmod hn ω hω S hS u q hq {t | θ t ≠ 0} hT (q t₀)
    fun t ht => ?_
  exact ZMod.val_injective _
    (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((h1 t ht).trans (h1 t₀ ht₀).symm))
end GlobalTheory
