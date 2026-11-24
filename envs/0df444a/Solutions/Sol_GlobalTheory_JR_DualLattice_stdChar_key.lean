-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.stdChar_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:25.456824+00:00
-- url     : https://prove2.me/submissions/be305ac1-582b-4f2b-a38f-8011e63b337c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F)
    (h : ∀ c : F, ‖c‖ ≤ 1 → ψ (c * y) = 1) : ‖y‖ ≤ 1 := by
  by_contra hy
  push Not at hy
  obtain ⟨x0, hx0, hx1⟩ := hψ.2
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
  have hinv : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy
  have := h _ (hx1 _ hinv)
  rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  exact hx0 this
end GlobalTheory.JR.DualLattice
