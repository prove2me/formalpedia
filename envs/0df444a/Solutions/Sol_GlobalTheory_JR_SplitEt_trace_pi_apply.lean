-- Prove2me | solution 1 for GlobalTheory.JR.SplitEt.trace_pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:46.554796+00:00
-- url     : https://prove2.me/submissions/3f2fc295-639a-4b6f-a14a-b7936fa4316a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SplitEt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.JR.SplitEt
theorem _root_.solution (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E (Fin r))]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]
end GlobalTheory.JR.SplitEt
