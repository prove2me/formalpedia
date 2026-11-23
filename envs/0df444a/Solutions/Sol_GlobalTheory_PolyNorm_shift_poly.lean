-- Prove2me | solution 1 for GlobalTheory.PolyNorm.shift_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:55.159837+00:00
-- url     : https://prove2.me/submissions/9f1d13d1-9167-4c4e-8b2f-63f49371853f

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
theorem _root_.solution (F : ℤ[X]) : ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + 1)) (F.map (Int.castRingHom ℚ[X]) + C X), fun t => ?_⟩
  rw [hN (F.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · rw [← C_eq_natCast, natDegree_add_C]; omega
end GlobalTheory.PolyNorm
