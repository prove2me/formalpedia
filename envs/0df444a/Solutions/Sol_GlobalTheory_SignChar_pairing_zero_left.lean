-- Prove2me | solution 1 for GlobalTheory.SignChar.pairing_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:16:45.773337+00:00
-- url     : https://prove2.me/submissions/40fc0efd-33e8-4105-b504-126f3b713a72

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique


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
theorem _root_.solution (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz
end GlobalTheory.SignChar
