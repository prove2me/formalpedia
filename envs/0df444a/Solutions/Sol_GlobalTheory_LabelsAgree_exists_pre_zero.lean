-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.exists_pre_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:06.237904+00:00
-- url     : https://prove2.me/submissions/10ea62d1-b1b9-41a8-9358-ac786bf311c8

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
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n) (J : NumD.Iso N N')
namespace GlobalTheory.LabelsAgree
theorem _root_.solution (hA : μ.A) (hG : μ.OnG J) {j : ℕ} {a : N'.QT (n ^ j)} (ha : a.1.1 = 1) :
    ∃ p, μ.r (n ^ j) p a ∧ TR J p a := by
  obtain ⟨p₀, h₀⟩ := μ.cotot j a
  obtain ⟨z, hz⟩ := (hA.2 j p₀ a h₀).1.2 ⟨0, by rw [ha]; simp⟩
  have h1 : μ.r (n ^ j) (p₀ * N.qTriv _ (-z)) a :=
    (μ.eqv _ p₀ _ a a h₀ ((N.qEq_iff _ _).2 ⟨-z, rfl⟩)).2 ((N'.qEq_equivalence _).refl a)
  have h2 : (p₀ * N.qTriv _ (-z)).1.1 = 1 := by
    change p₀.1.1.toAdd + n ^ j • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  refine ⟨_, h1, ?_, hG j _ _ h1 h2 ha⟩
  rw [h2, ha, toAdd_one, toAdd_one, map_zero]
end GlobalTheory.LabelsAgree
