-- Prove2me | solution 1 for GlobalTheory.HeckeLocInt.small_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:59.351206+00:00
-- url     : https://prove2.me/submissions/81ce1708-62af-4d30-a0b8-80af56890bd7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.HeckeLocInt
open Matrix
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.HeckeLocInt
theorem _root_.solution {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) < 1) :
    ∀ i j, Valued.v ((M * N) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero (fun l _ => ?_)
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hM i l)) (hN l j)
end GlobalTheory.HeckeLocInt
