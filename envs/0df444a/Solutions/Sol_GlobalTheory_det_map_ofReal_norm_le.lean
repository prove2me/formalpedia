-- Prove2me | solution 1 for GlobalTheory.det_map_ofReal_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:17.324405+00:00
-- url     : https://prove2.me/submissions/9964092e-b31e-4796-af30-5c6866ea5fc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPow
import Theorems.Thm_GlobalTheory_abs_entry_le_of_psd_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  intro g Y M _ hY hMY
  have hmap : (Y.map Complex.ofReal).det = ((Y.det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom Y
    exact this.symm
  rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := M) (A := Y)
    (fun i j => abs_entry_le_of_psd_le g Y M hY hMY i j)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h
end GlobalTheory
