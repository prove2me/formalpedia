-- Prove2me | solution 1 for GlobalTheory.EtIsom.herm_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:49.241832+00:00
-- url     : https://prove2.me/submissions/fc43bfbf-b19a-4b56-9896-4bb704e5a327

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
theorem _root_.solution (M : Matrix (Fin r) (Fin r) E) (hM : M.conjTranspose = M) (b : Fin r → E) (i k : ℕ) :
    star (M ^ i *ᵥ b) ⬝ᵥ (M ^ k *ᵥ b) = star b ⬝ᵥ (M ^ (i + k) *ᵥ b) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_pow, hM, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, pow_add]
end GlobalTheory.EtIsom
