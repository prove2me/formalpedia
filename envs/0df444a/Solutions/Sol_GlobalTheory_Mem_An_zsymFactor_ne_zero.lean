-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsymFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:46.519497+00:00
-- url     : https://prove2.me/submissions/079ced16-c177-481f-a9bb-46d4dd8266fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
import Theorems.Thm_GlobalTheory_Mem_An_zsym_gammaFactor_ne_zero
import Theorems.Thm_GlobalTheory_Mem_An_zsym_rootNumber_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
variable [NeZero q]
namespace GlobalTheory.Mem.An
theorem _root_.solution {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : zsymFactor χ s ≠ 0 := by
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have g3 := zsym_rootNumber_ne_zero hχ
  have g4 : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    simp [cpow_eq_zero_iff, NeZero.ne q]
  unfold zsymFactor
  exact div_ne_zero (mul_ne_zero (mul_ne_zero g4 g3) (inv_ne_zero g1)) (inv_ne_zero g2)
end GlobalTheory.Mem.An
