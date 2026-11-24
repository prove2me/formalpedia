-- Prove2me | solution 1 for GlobalTheory.PolyNorm.det_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:09.253889+00:00
-- url     : https://prove2.me/submissions/d2c2dff9-6014-4961-ac56-1b9e44100499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_eq_prod_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {m : ℕ} (V : Matrix (Fin m) (Fin m) K)
    (b : Multiset K) (hb : V.charpoly = (b.map fun x => X - C x).prod) (F : K[X]) :
    (aeval V F).det = (b.map fun x => F.eval x).prod := by
  have hc : Multiset.card b = m := by
    rw [← natDegree_multiset_prod_X_sub_C_eq_card b, ← hb]; simp
  refine eq_prod_of_mul (Matrix.detMonoidHom.comp (aeval V : K[X] →ₐ[K] _).toMonoidHom) b
    (fun c => ?_) (fun β => ?_) F
  · simp [hc, Algebra.algebraMap_eq_smul_one]
  · have := congrArg (eval β) hb
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using this
end GlobalTheory.PolyNorm
