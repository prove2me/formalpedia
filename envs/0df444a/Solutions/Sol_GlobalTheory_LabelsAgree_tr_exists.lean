-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.tr_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:54:40.878823+00:00
-- url     : https://prove2.me/submissions/4336f4f7-08c9-4d66-949f-1086b530ea97

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
import Theorems.Thm_GlobalTheory_LabelsAgree_rel_unique
import Theorems.Thm_GlobalTheory_LabelsAgree_rel_pow
import Theorems.Thm_GlobalTheory_T_hom_transport_alt


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
variable {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N')
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {k : ℕ} (p : N.QT k) : ∃ p', TR J p p' := by
  obtain ⟨g', hg'⟩ := ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).1 p.1.2).exists
  have h1 := rel_pow J hg' k
  rw [N.mem_QT.1 p.2] at h1
  have h2 : J.Rel (N.io p.1.1.toAdd) (N'.io (J.e p.1.1.toAdd)) := (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.1 _
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g'), rel_unique J h1 h2⟩, rfl, hg'⟩
end GlobalTheory.LabelsAgree
