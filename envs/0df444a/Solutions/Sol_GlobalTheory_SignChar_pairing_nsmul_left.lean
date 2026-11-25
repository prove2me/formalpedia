-- Prove2me | solution 1 for GlobalTheory.SignChar.pairing_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:35:14.422317+00:00
-- url     : https://prove2.me/submissions/b88afafd-adae-4daf-b6b7-02068044bfef

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight
import Theorems.Thm_GlobalTheory_SignChar_pairing_zero_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.SignChar
variable {R₀ : Type} [CommRing R₀]
variable (B : BX R₀) {R : LAlg R₀}
namespace GlobalTheory.SignChar
theorem _root_.solution (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h
end GlobalTheory.SignChar
