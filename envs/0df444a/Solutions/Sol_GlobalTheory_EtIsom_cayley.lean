-- Prove2me | solution 1 for GlobalTheory.EtIsom.cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:47.491258+00:00
-- url     : https://prove2.me/submissions/0bc92300-e78b-4a13-99f3-50c8579c36c1

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
theorem _root_.solution (M : Matrix (Fin r) (Fin r) E) : M ^ r + ∑ i : Fin r, M.charpoly.coeff i • M ^ (i : ℕ) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [M.charpoly_monic.as_sum, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  simpa [Finset.sum_range, Algebra.smul_def] using h
end GlobalTheory.EtIsom
