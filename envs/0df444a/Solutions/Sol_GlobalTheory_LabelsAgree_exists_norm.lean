-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:35.250127+00:00
-- url     : https://prove2.me/submissions/66188bbe-3324-4470-b7d7-c14c26840897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n) (J : NumD.Iso N N')
namespace GlobalTheory.LabelsAgree
theorem _root_.solution (hB : μ.B J.e) (j : ℕ) (p : N.QT (n ^ j)) :
    ∃ p', μ.r (n ^ j) p p' ∧ p'.1.1.toAdd = J.e p.1.1.toAdd := by
  obtain ⟨p', hp'⟩ := μ.tot j p
  obtain ⟨z, hz⟩ := hB j p p' hp'
  refine ⟨p' * N'.qTriv _ (-z), (μ.eqv _ p p p' _ hp' ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ j • (-z) = _
  rw [hz, smul_neg, add_neg_cancel_right]
end GlobalTheory.LabelsAgree
