-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.defect_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:10.405863+00:00
-- url     : https://prove2.me/submissions/9fc400ee-d634-4e54-ab17-2b6ecb2c5fb6

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
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_exists
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_wp
import Theorems.Thm_GlobalTheory_LabelsAgree_wp_mul_left
import Theorems.Thm_GlobalTheory_LabelsAgree_wp_mul_right
import Theorems.Thm_GlobalTheory_LabelsAgree_wp_tor
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_mul_right


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
theorem _root_.solution {k : ℕ} {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') : d.1.2.s (J.e x') = d'.1.2.s (J.e x) := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.wp _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [wp_mul_left, wp_mul_right, tr_wp J ha ha', mul_assoc, mul_eq_left, N'.wp_swap, wp_tor h'.1 h'.2.1,
    wp_tor h.1 h.2.1, inv_mul_eq_one] at h1
  have e : (a' * d').1.1.toAdd = J.e x' := by
    change (a'.1.1 * d'.1.1).toAdd = _
    rw [h'.1, mul_one, ha'.1, hp']
  rw [← e, ← h1, ha.1, hp]
end GlobalTheory.LabelsAgree
