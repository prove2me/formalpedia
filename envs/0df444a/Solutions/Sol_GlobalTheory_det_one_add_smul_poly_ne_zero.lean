-- Prove2me | solution 1 for GlobalTheory.det_one_add_smul_poly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:01.315265+00:00
-- url     : https://prove2.me/submissions/ecb70aa0-84e9-4259-8c7a-b2d93ea72bb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero
import Theorems.Thm_GlobalTheory_det_one_add_smul_poly_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) ≠ 0 := by
  intro h
  have := det_one_add_smul_poly_eval M 0
  rw [h] at this
  simp at this
end GlobalTheory
