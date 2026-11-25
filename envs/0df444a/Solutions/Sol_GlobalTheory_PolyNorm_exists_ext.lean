-- Prove2me | solution 1 for GlobalTheory.PolyNorm.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:55.90583+00:00
-- url     : https://prove2.me/submissions/b8bb9237-b6b0-4fa3-be7a-f4fccac80a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_mul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_one
import Theorems.Thm_GlobalTheory_PolyNorm_ev_compat

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
theorem _root_.solution (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) (K : Type) [CommRing K]
    [Algebra ℚ K] : ∃ M : K[X] →* K, ∀ s (F : K[X]), F.natDegree < s → M F = ev (Φ s) F := by
  refine ⟨⟨⟨fun F => ev (Φ (F.natDegree + 1)) F, ev_one N Φ hN h1 _⟩, fun F G => ?_⟩,
    fun s F h => (ev_compat N Φ hN h1 hm s F h).symm⟩
  dsimp only
  rw [← ev_mul N Φ hN hm F.natDegree G.natDegree _ (Nat.lt_succ_self _) F G le_rfl le_rfl,
    ← ev_compat N Φ hN h1 hm]
  exact Nat.lt_succ_of_le natDegree_mul_le
end GlobalTheory.PolyNorm
