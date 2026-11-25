-- Prove2me | solution 1 for GlobalTheory.PolyNorm.ev_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:13.672599+00:00
-- url     : https://prove2.me/submissions/8dcfe18a-a332-43ba-9b9a-00a95b177c6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_mul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_one

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
theorem _root_.solution (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K]
    [Algebra ℚ K] (s : ℕ) (F : K[X]) (hF : F.natDegree < s) :
    ev (Φ s) F = ev (Φ (F.natDegree + 1)) F := by
  have := ev_mul N Φ hN hm F.natDegree 0 s hF F 1 le_rfl (by simp)
  rwa [ev_one N Φ hN h1, mul_one, mul_one] at this
end GlobalTheory.PolyNorm
