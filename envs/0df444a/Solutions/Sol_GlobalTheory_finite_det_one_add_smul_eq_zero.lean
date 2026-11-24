-- Prove2me | solution 1 for GlobalTheory.finite_det_one_add_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:57.628688+00:00
-- url     : https://prove2.me/submissions/dd808283-5495-4e55-9c99-130dd03a9be8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero
import Theorems.Thm_GlobalTheory_det_one_add_smul_poly_eval
import Theorems.Thm_GlobalTheory_det_one_add_smul_poly_ne_zero

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
    {z : ℂ | det (1 + z • M) = 0}.Finite := by
  refine (Polynomial.rootSet_finite (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet_of_ne (det_one_add_smul_poly_ne_zero M)]
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
  rw [det_one_add_smul_poly_eval]
  exact hz
end GlobalTheory
