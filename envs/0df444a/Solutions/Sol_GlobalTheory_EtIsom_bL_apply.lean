-- Prove2me | solution 1 for GlobalTheory.EtIsom.bL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:19.515222+00:00
-- url     : https://prove2.me/submissions/78ae060e-24ec-443f-a7f1-7eda5be6eb0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_bK_apply

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
theorem _root_.solution (hG : A.IsGen τ p) (i : Fin r) : bL A hG i = algebraMap A.K A.L (τ ^ (i : ℕ)) := by
  rw [bL, IsBaseChange.basis_apply, bK_apply]; rfl
end GlobalTheory.EtIsom
