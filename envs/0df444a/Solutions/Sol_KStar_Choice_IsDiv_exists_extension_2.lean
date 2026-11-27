-- Prove2me | solution 2 for KStar.Choice.IsDiv.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:20.863869+00:00
-- url     : https://prove2.me/submissions/7c99c564-2240-4303-a748-53e0263243ad

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_ExtAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Choice
namespace KStar.Choice
namespace IsDiv
theorem _root_.solution {G A : Type*} [CommGroup G] [CommGroup A] (hA : IsDiv A)
    (H : Subgroup G) (f : H →* A) : ∃ F : G →* A, ∀ h : H, F h = f h := by
  have hsurj : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective fun a : Additive A => n • a := by
    intro n hn x
    obtain ⟨y, hy⟩ := hA n.natAbs (Int.natAbs_ne_zero.mpr hn) (Additive.toMul x)
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul y, ?_⟩
      rw [h]
      change Additive.ofMul (y ^ ((n.natAbs : ℕ) : ℤ)) = x
      rw [zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
    · refine ⟨Additive.ofMul y⁻¹, ?_⟩
      rw [h]
      change Additive.ofMul (y⁻¹ ^ (-((n.natAbs : ℕ) : ℤ))) = x
      rw [inv_zpow', neg_neg, zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
  letI : DivisibleBy (Additive A) ℤ := divisibleByOfSMulRightSurj _ _ hsurj
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) Subtype.val_injective (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul x))
end IsDiv
end KStar.Choice
