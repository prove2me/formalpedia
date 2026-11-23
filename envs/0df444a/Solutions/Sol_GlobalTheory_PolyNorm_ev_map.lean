-- Prove2me | solution 1 for GlobalTheory.PolyNorm.ev_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:05.827861+00:00
-- url     : https://prove2.me/submissions/75025ad5-3a49-47c9-bca2-7793d7eda9be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

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
theorem _root_.solution {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K L : Type} [CommRing K] [Algebra ℚ K]
    [CommRing L] [Algebra ℚ L] (φ : K →+* L) (F : K[X]) : φ (ev Φ F) = ev Φ (F.map φ) := by
  unfold ev
  rw [MvPolynomial.map_aeval, MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext_rat _ _
  · ext i; simp
end GlobalTheory.PolyNorm
