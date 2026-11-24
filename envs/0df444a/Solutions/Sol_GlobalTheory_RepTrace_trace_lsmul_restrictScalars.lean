-- Prove2me | solution 1 for GlobalTheory.RepTrace.trace_lsmul_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:32.08174+00:00
-- url     : https://prove2.me/submissions/40c119f2-6535-4464-b53d-d64311a2beaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepTraceEqMulTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.RepTrace
namespace GlobalTheory.RepTrace
theorem _root_.solution {K L V : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V] [FiniteDimensional L V] (a : L) :
    LinearMap.trace K V ((LinearMap.lsmul L V a).restrictScalars K) =
      (Module.finrank L V : K) * Algebra.trace K L a := by
  classical
  let b := Module.finBasis L V
  let c := Module.finBasis K L
  rw [LinearMap.trace_eq_matrix_trace K (c.smulTower b), Algebra.trace_eq_matrix_trace c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.smulTower_repr_mk, smul_smul, Finsupp.single_apply, Finset.mul_sum, mul_comm]
end GlobalTheory.RepTrace
