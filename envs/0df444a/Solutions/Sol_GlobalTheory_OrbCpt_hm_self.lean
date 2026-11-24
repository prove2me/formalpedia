-- Prove2me | solution 1 for GlobalTheory.OrbCpt.hm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:43.764117+00:00
-- url     : https://prove2.me/submissions/184cc090-1f75-411f-b38f-a0d97abfd98f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_gsum_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
namespace GlobalTheory.OrbCpt
theorem _root_.solution (p : k[X]) (X : Matrix (Fin r) (Fin r) k) :
    hm p X X = aeval X (derivative p) := by
  have h1 : (derivative p).natDegree < p.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le p) (by omega)
  rw [aeval_eq_sum_range' h1, hm, Finset.sum_range_succ', show gsum X X 0 = 0 from rfl, smul_zero,
    add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [gsum_self, coeff_derivative, smul_smul]
  congr 1; push_cast; ring
end GlobalTheory.OrbCpt
