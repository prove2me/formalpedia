-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.toZModPow_toPadicInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:48.304558+00:00
-- url     : https://prove2.me/submissions/65d06653-d8ee-43b9-969d-0abdd5110c98

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
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (k : ℕ) (x : ℤ̂) :
    PadicInt.toZModPow k (toPadicInt ℓ x) =
      ProfiniteInteger.proj (primePowPNat ℓ k) x :=
  RingHom.congr_fun (PadicInt.lift_spec _ k) x
end GroundTheory.Global.Cyclotomic
