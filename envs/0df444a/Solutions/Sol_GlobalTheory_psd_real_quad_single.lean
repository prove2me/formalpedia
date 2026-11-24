-- Prove2me | solution 1 for GlobalTheory.psd_real_quad_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:38.25249+00:00
-- url     : https://prove2.me/submissions/979102d4-8625-44cc-b65d-be7b527700cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPow

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
theorem _root_.solution (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by
  have h := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
    single_dotProduct, dotProduct_single] at h
  simp [Pi.single_apply, hij, hij.symm] at h
  linarith
end GlobalTheory
