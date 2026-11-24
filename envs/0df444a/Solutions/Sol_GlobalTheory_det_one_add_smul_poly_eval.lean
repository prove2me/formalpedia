-- Prove2me | solution 1 for GlobalTheory.det_one_add_smul_poly_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:49.082081+00:00
-- url     : https://prove2.me/submissions/6f6bda7d-e9dc-44a6-97df-4f30da56ca40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero

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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Polynomial.eval z (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) = det (1 + z • M) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp [mul_comm]
end GlobalTheory
