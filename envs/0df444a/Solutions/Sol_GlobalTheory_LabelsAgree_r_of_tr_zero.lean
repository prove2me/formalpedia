-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.r_of_tr_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:56.797077+00:00
-- url     : https://prove2.me/submissions/ab9b75ec-ceeb-4bdd-a600-183e4920b3cc

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
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_unique
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_norm

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
theorem _root_.solution (hB : μ.B J.e) (hG : μ.OnG J) {j : ℕ} {p : N.QT (n ^ j)} {a : N'.QT (n ^ j)}
    (hp : p.1.1 = 1) (ha : TR J p a) : μ.r (n ^ j) p a := by
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p
  have h3 : p'.1.1 = 1 := by
    rw [hp, toAdd_one, map_zero] at h2
    exact h2
  rw [tr_unique J ha ⟨h2, hG j p p' h1 hp h3⟩]
  exact h1
end GlobalTheory.LabelsAgree
