-- Prove2me | solution 1 for GlobalTheory.eigDim_aeval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:02.956966+00:00
-- url     : https://prove2.me/submissions/a24adada-c777-438f-889b-43d010102447

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    (aeval M f).map φ = aeval (M.map φ) (f.map φ) := by
  have h : (φ.mapMatrix : Matrix n n K →+* Matrix n n L).comp (algebraMap K (Matrix n n K)) =
      (algebraMap L (Matrix n n L)).comp φ := by
    ext r i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  change φ.mapMatrix (Polynomial.eval₂ (algebraMap K (Matrix n n K)) M f) =
    Polynomial.eval₂ (algebraMap L (Matrix n n L)) (M.map φ) (f.map φ)
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, h]
  rfl
end GlobalTheory
