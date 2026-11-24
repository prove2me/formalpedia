-- Prove2me | solution 1 for GlobalTheory.EtIsom.mat_herm_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:17:42.497564+00:00
-- url     : https://prove2.me/submissions/ba380719-8fb3-4dc1-af99-04cc268e79b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_mat_mulVec

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
theorem _root_.solution {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hj : A.IsIsom x j) (u v : Fin r → E) :
    star (mat A (τ := τ) j *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (mat A (τ := τ) j *ᵥ v) := by
  obtain ⟨z, rfl⟩ := j.surjective u
  obtain ⟨z', rfl⟩ := j.surjective v
  rw [mat_mulVec, mat_mulVec, hj, hj, star_mul', A.star_K]
  congr 1
  ring
end GlobalTheory.EtIsom
