-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.modCharacter_eq_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:44.24388+00:00
-- url     : https://prove2.me/submissions/15063e71-c749-4405-9e93-0bfef87e8d8a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character

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
variable {n : ℕ} [NeZero n]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)}
    {c : ZMod n} (h : σ ζ = ζ ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine modCharacter_unique σ fun t ht => ?_
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ht
  rw [map_pow, h, ← pow_mul, ← pow_mul, mul_comm]
end GroundTheory.Global.Cyclotomic
