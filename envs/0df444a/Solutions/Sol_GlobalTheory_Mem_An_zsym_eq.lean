-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsym_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:46.270036+00:00
-- url     : https://prove2.me/submissions/12502e46-e2c4-47d6-ac03-1f398f829a51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
import Theorems.Thm_GlobalTheory_Mem_An_zsym_gammaFactor_ne_zero

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
theorem _root_.solution {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) : χ.LFunction s = zsymFactor χ s * χ⁻¹.LFunction (1 - s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : 1 - s ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; simp at h1
  have h2 := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h2
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0),
    χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hs1), h2, zsymFactor]
  field_simp
end GlobalTheory.Mem.An
