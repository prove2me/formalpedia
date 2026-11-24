-- Prove2me | solution 1 for GlobalTheory.EtIsom.mat_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:03.856601+00:00
-- url     : https://prove2.me/submissions/67e757af-5cbf-4a06-8e3a-950944a6422e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_mat_herm_form

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
theorem _root_.solution {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hj : A.IsIsom x j) :
    IsSelfAdjoint (mat A (τ := τ) j) := by
  ext k i
  have h := mat_herm_form A (τ := τ) hj (Pi.single k 1) (Pi.single i 1)
  simp [Matrix.mulVec_single, dotProduct_single, single_dotProduct] at h
  simpa [Matrix.star_apply, Matrix.conjTranspose_apply] using h
end GlobalTheory.EtIsom
