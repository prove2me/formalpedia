-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.toGQ_sl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:02.392144+00:00
-- url     : https://prove2.me/submissions/dc78bb65-4385-402f-a535-a65182f6858a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
variable {R : Type} [CommRing R]
namespace GlobalTheory.KZ.Betti
theorem _root_.solution (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_pos
  unfold toGQ
  rw [dif_pos h]
  apply Subtype.ext
  apply Units.ext
  rfl
end GlobalTheory.KZ.Betti
