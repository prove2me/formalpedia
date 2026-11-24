-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.eta_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:37.199525+00:00
-- url     : https://prove2.me/submissions/d7ac5e66-6f8a-47c6-828a-74e7e2222597

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
theorem _root_.solution [Unram F E] (A : Et F E) : A.etaK (-1) = 1 := by
  rw [Et.etaK, eta]
  refine if_pos ⟨1, ?_⟩
  have h : Algebra.norm F (-1 : A.K) * Algebra.norm F (-1 : A.K) = 1 := by
    rw [← map_mul]; simp
  have h' := congrArg norm h
  rw [norm_mul, norm_one] at h'
  have h0 : 0 ≤ ‖Algebra.norm F (-1 : A.K)‖ := norm_nonneg _
  simp only [norm_one, one_pow]
  nlinarith
end GlobalTheory.JR.EtFacts
