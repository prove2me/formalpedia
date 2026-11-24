-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.defect_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:09.315213+00:00
-- url     : https://prove2.me/submissions/77012cd9-facb-4ca5-9c71-0f5b5df77907

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
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_mul
import Theorems.Thm_GlobalTheory_LabelsAgree_r_unique
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_mul


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
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' d'' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') (h'' : Defect μ J k (x + x') d'') : d'' = d * d' := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.mul _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [mul_mul_mul_comm] at h1
  have h2 := h''.2.2 (p * p') (a * a') (by rw [← hp, ← hp']; rfl) (tr_mul J ha ha')
  refine mul_left_cancel (r_unique μ hk h2 h1 ?_)
  change a.1.1 * a'.1.1 * d''.1.1 = a.1.1 * a'.1.1 * (d.1.1 * d'.1.1)
  rw [h.1, h'.1, h''.1, mul_one (1 : Multiplicative N'.X)]
end GlobalTheory.LabelsAgree
