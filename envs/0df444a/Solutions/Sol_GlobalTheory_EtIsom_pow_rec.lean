-- Prove2me | solution 1 for GlobalTheory.EtIsom.pow_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:20:36.350609+00:00
-- url     : https://prove2.me/submissions/a3db1deb-10a5-4428-9f9e-d7390f519609

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry

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
theorem _root_.solution (hG : A.IsGen τ p) (m : ℕ) :
    τ ^ (m + r) = -∑ i, algebraMap F A.K (p i) * τ ^ (m + (i : ℕ)) := by
  have h := congrArg (fun t => τ ^ m * t) hG.2.2
  simp only [mul_add, Finset.mul_sum, mul_zero, Algebra.smul_def] at h
  rw [eq_neg_iff_add_eq_zero, ← h, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring
end GlobalTheory.EtIsom
