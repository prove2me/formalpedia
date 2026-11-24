-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.nonunits_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:03.784772+00:00
-- url     : https://prove2.me/submissions/ab5a684a-ab70-483e-bc0e-79ce779dacb2

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
import Theorems.Thm_GlobalTheory_T_addHaar_proper_submodule_eq_zero_moduleTopology


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
theorem _root_.solution [U : Unram F E] (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure) :
    μ {t | ¬ IsUnit t} = 0 := by
  have := U.lcF
  have : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite A.K
  have hsub : {t : A.K | ¬ IsUnit t} ⊆ ⋃ m ∈ {I : Ideal A.K | I.IsMaximal}, (m : Set A.K) := by
    intro t ht
    obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits (show t ∈ nonunits A.K from ht)
    exact Set.mem_biUnion hm htm
  refine measure_mono_null hsub ((measure_biUnion_null_iff hfin.countable).2 fun m hm => ?_)
  have h := GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology F A.K μ hμ (m.restrictScalars F) (fun h => hm.ne_top ?_)
  · exact h
  · rw [Ideal.eq_top_iff_one]
    have : (1 : A.K) ∈ m.restrictScalars F := h ▸ Submodule.mem_top
    exact this
end GlobalTheory.JR.EtFacts
