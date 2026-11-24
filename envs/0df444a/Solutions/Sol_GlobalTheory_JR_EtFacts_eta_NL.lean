-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.eta_NL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:54.066306+00:00
-- url     : https://prove2.me/submissions/c325fcf5-781f-4399-bfe9-c611a062918d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsOpenFiniteEtaleHermitianPairOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFacts
import Theorems.Thm_GlobalTheory_JR_EtFacts_normE
import Theorems.Thm_GlobalTheory_JR_EtFacts_free_L_E
import Theorems.Thm_GlobalTheory_JR_EtFacts_free_L_K

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtFacts
namespace GlobalTheory.JR.EtFacts
theorem _root_.solution [U : Unram F E] (A : Et F E) (y : A.L) : A.etaK (A.NL y) = 1 := by
  have := free_L_E A
  have := free_L_K A
  have h1 : Algebra.norm F (A.NL y) = Algebra.norm F (Algebra.norm E y) := by
    rw [Et.NL, Algebra.norm_norm, Algebra.norm_norm]
  rw [Et.etaK, h1, eta]
  obtain ⟨x, hx⟩ := U.unram (Algebra.norm E y)
  have hx2 : ‖Algebra.norm F (Algebra.norm E y)‖ = ‖x‖ ^ 2 := by
    rw [← norm_algebraMap' E, normE, norm_mul, U.norm_star, hx, sq]
  rw [if_pos ⟨x, hx2⟩]
end GlobalTheory.JR.EtFacts
