-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.tr_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:09:51.895713+00:00
-- url     : https://prove2.me/submissions/3df2dc44-0f14-4ac8-8855-ba8c6287e317

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
theorem _root_.solution {k : ℕ} {p : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J p b) : a = b :=
  Subtype.ext (Prod.ext (ha.1.trans hb.1.symm) (rel_unique J ha.2 hb.2))
end GlobalTheory.LabelsAgree
