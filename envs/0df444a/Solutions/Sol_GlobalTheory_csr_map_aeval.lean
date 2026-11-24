-- Prove2me | solution 1 for GlobalTheory.csr_map_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:54.675211+00:00
-- url     : https://prove2.me/submissions/b593fd81-1e9f-4a2f-8c08-a3ac332c2e49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p).map σ = aeval (A.map σ) (p.map σ) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := p.natDegree + 1)]
  · rw [← RingHom.mapMatrix_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow : (A ^ i).map σ = (A.map σ) ^ i := by
      rw [← RingHom.mapMatrix_apply, map_pow]; rfl
    rw [coeff_map, RingHom.mapMatrix_apply, ← hpow]
    ext a b
    simp [Matrix.smul_apply]
  · exact Nat.lt_succ_of_le (natDegree_map_le)
end GlobalTheory
