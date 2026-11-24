-- Prove2me | solution 1 for GlobalTheory.EtIsom.trace_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:01.600805+00:00
-- url     : https://prove2.me/submissions/38f5c7b8-5eca-46c9-82d9-d0a03cce69e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_bK_apply
import Theorems.Thm_GlobalTheory_EtIsom_bL_apply
import Theorems.Thm_GlobalTheory_EtIsom_bL_repr

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
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution (hG : A.IsGen τ p) (c : A.K) :
    Algebra.trace E A.L (algebraMap A.K A.L c) = algebraMap F E (Algebra.trace F A.K c) := by
  rw [Algebra.trace_eq_matrix_trace (bL A hG), Algebra.trace_eq_matrix_trace (bK A hG), Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  rw [bL_apply, ← map_mul, bL_repr, bK_apply]
end GlobalTheory.EtIsom
