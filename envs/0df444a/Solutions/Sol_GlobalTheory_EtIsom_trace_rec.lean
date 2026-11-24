-- Prove2me | solution 1 for GlobalTheory.EtIsom.trace_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:49.921052+00:00
-- url     : https://prove2.me/submissions/0415d0c0-209c-4a63-80de-a652572952ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_pow_rec

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
theorem _root_.solution (hG : A.IsGen τ p) (a : A.K) (m : ℕ) :
    algebraMap F E (Algebra.trace F A.K (τ ^ (m + r) * a)) =
      -∑ i, algebraMap F E (p i) • algebraMap F E (Algebra.trace F A.K (τ ^ (m + (i : ℕ)) * a)) := by
  rw [pow_rec A hG, neg_mul, Finset.sum_mul, map_neg, map_sum, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, map_mul, smul_eq_mul]
end GlobalTheory.EtIsom
