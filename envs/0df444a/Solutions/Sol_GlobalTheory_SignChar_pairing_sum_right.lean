-- Prove2me | solution 1 for GlobalTheory.SignChar.pairing_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:42:30.380827+00:00
-- url     : https://prove2.me/submissions/7d406565-3aba-4e9e-b3b9-141be78af5b0

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
theorem _root_.solution {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_right B N x hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_right N _ _ _ _ _ (h a) ih
end GlobalTheory.SignChar
