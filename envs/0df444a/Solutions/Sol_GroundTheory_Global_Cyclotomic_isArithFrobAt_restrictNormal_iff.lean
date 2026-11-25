-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isArithFrobAt_restrictNormal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:31.540493+00:00
-- url     : https://prove2.me/submissions/2e46e5ac-d183-4ce4-9055-274eb6e04b53

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isArithFrobAt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
variable (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (rootsOfUnityField m)))
  [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (hm : ¬ p ∣ m) (σ : Gal(ℚ̄/ℚ)) :
    IsArithFrobAt ℤ (σ.restrictNormal (rootsOfUnityField m)) P ↔
      (modCharacter m σ : ZMod m) = p := by
  rw [isArithFrobAt_iff p _ P hm]
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ m
    let ζ' : rootsOfUnityField m := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
    have hζ' : ζ' ^ m = 1 := Subtype.ext hζ.pow_eq_one
    have := congrArg (algebraMap (rootsOfUnityField m) ℚ̄) (h ζ' hζ')
    rw [AlgEquiv.restrictNormal_commutes, map_pow] at this
    refine modCharacter_eq_of_apply hζ ?_
    rw [pow_val_natCast hζ.pow_eq_one]
    exact this
  · intro h x hx
    have hx' : (algebraMap (rootsOfUnityField m) ℚ̄ x) ^ m = 1 := by
      rw [← map_pow, hx, map_one]
    apply (algebraMap (rootsOfUnityField m) ℚ̄).injective
    rw [AlgEquiv.restrictNormal_commutes, map_pow, modCharacter_spec σ hx', h,
      pow_val_natCast hx']
end GroundTheory.Global.Cyclotomic
