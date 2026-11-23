-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.key_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:05.937045+00:00
-- url     : https://prove2.me/submissions/6ff6febc-2bec-475d-8070-3a80e9e7ebde

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
theorem _root_.solution (A : Et F E) (a x : A.Kˣ) : (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
    (QuotientGroup.mk x : A.Kˣ ⧸ (EtMeas.normU A).range) = QuotientGroup.mk a := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨hy.unit, Units.ext ?_⟩
    simp [h, Et.NL, EtMeas.normU]
  · rintro ⟨y, h⟩
    refine ⟨y, y.isUnit, ?_⟩
    have := congrArg Units.val h
    simp only [EtMeas.normU, Units.coe_map, Units.val_mul] at this
    rw [Et.NL, this]; simp
end GlobalTheory.JR.EtFacts
