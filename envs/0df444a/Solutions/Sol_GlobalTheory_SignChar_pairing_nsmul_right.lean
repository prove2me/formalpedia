-- Prove2me | solution 1 for GlobalTheory.SignChar.pairing_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:39.972508+00:00
-- url     : https://prove2.me/submissions/3d7dd6ca-a17a-4219-82f8-0c9243042505

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight
import Theorems.Thm_GlobalTheory_SignChar_pairing_zero_right
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_right


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
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_right B N x h.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_right N _ _ _ _ _ ih h
end GlobalTheory.SignChar
