-- Prove2me | solution 1 for GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:22.64443+00:00
-- url     : https://prove2.me/submissions/98320bcf-bcf7-478e-8082-9dfbe40706e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrixStatement
import Theorems.Thm_GlobalTheory_det_traceGram_blockMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ} (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E'), (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  first | exact @GlobalTheory.det_traceGram_blockMatrix | exact GlobalTheory.det_traceGram_blockMatrix | (intros; apply GlobalTheory.det_traceGram_blockMatrix <;> assumption)
end _root_.GlobalTheory.T
