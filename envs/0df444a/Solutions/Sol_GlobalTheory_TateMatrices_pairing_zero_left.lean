-- Prove2me | solution 1 for GlobalTheory.TateMatrices.pairing_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:19.00037+00:00
-- url     : https://prove2.me/submissions/8093855d-ae92-4f35-8148-515994d357b6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
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
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
namespace GlobalTheory.TateMatrices
theorem _root_.solution (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz
end GlobalTheory.TateMatrices
