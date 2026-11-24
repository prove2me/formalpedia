-- Prove2me | solution 1 for GlobalTheory.EtIsom.mat_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:50.588319+00:00
-- url     : https://prove2.me/submissions/5bf8d538-940a-4a95-ae90-8f929cd36981

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
theorem _root_.solution (M : Matrix (Fin r) (Fin r) E) (q : Fin r → E) (h : M ^ r + ∑ i : Fin r, q i • M ^ (i : ℕ) = 0)
    (v : Fin r → E) (m : ℕ) : M ^ (m + r) *ᵥ v = -∑ i, q i • (M ^ (m + (i : ℕ)) *ᵥ v) := by
  have h1 := congrArg (fun N => (M ^ m * N) *ᵥ v) h
  simp only [mul_add, Finset.mul_sum, mul_smul_comm, ← pow_add, Matrix.add_mulVec, Matrix.sum_mulVec,
    Matrix.smul_mulVec, mul_zero, Matrix.zero_mulVec] at h1
  exact eq_neg_of_add_eq_zero_left h1
end GlobalTheory.EtIsom
