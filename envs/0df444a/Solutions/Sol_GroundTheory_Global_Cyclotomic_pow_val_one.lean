-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.pow_val_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:00.946736+00:00
-- url     : https://prove2.me/submissions/68390f14-7a4c-4e76-9649-521960b5214f

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
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) :
    t ^ (1 : ZMod n).val = t := by
  have := pow_val_natCast ht 1
  rwa [Nat.cast_one, pow_one] at this
end GroundTheory.Global.Cyclotomic
