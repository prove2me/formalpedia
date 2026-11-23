-- Prove2me | solution 1 for GlobalTheory.PolyNorm.ev_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:08.95239+00:00
-- url     : https://prove2.me/submissions/d6d7fbea-4450-42c3-beb4-7002d76d23bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_map

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
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN
namespace GlobalTheory.PolyNorm
theorem _root_.solution (h1 : N 1 = 1) {K : Type} [CommRing K] [Algebra ℚ K] (r : ℕ) :
    ev (Φ (r + 1)) (1 : K[X]) = 1 := by
  have := ev_map (Φ (r + 1)) (algebraMap ℚ K) ((1 : ℤ[X]).map (Int.castRingHom ℚ))
  rw [← hN _ _ (by simp), h1] at this
  simpa using this.symm
end GlobalTheory.PolyNorm
