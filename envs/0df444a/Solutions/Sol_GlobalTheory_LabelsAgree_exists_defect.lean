-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.exists_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:19.139982+00:00
-- url     : https://prove2.me/submissions/8fc0d838-d950-4aab-a949-2f276c8a8cd7

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
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_unique
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_mul
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_wp
import Theorems.Thm_GlobalTheory_LabelsAgree_eq_of_qEq
import Theorems.Thm_GlobalTheory_LabelsAgree_wp_mul_left
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_norm
import Theorems.Thm_GlobalTheory_LabelsAgree_r_of_tr_zero
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_pre_zero
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_mul
import Theorems.Thm_GlobalTheory_Ex_QStr_qStructure
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
theorem _root_.solution [IsAlgClosed C] {g g' : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (hT' : N'.Tors n g')
    (hA : μ.A) (hB : μ.B J.e) (hG : μ.OnG J) (j : ℕ) (x : N.X) : ∃ d, Defect μ J (n ^ j) x d := by
  have hn0 : n ^ j ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hn)
  obtain ⟨p₀, hp₀⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).2.2.1 x
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p₀
  obtain ⟨a₀, ha₀⟩ := tr_exists J p₀
  have e : p' = a₀ * (p' / a₀) := by simp
  have hd : (p' / a₀).1.1 = 1 := by
    change p'.1.1.toAdd - a₀.1.1.toAdd = 0
    rw [h2, ha₀.1, sub_self]
  refine ⟨p' / a₀, hd, ?_, fun p a hp ha => ?_⟩
  · obtain ⟨d₀, q1, q2, q3⟩ := ((GlobalTheory.Ex.QStr.qStructure C N' n g' hn hT' j).2.2.2.2.1 (p' / a₀)).1 fun q' hq' => by
      obtain ⟨q, r1, r2⟩ := exists_pre_zero μ J hA hG hq'
      have w1 := μ.wp _ _ _ _ _ h1 r1
      rw [e, wp_mul_left, tr_wp J ha₀ r2] at w1
      exact mul_eq_left.1 w1
    rw [eq_of_qEq hn0 q1 (hd.trans q2.symm)]
    exact q3
  · obtain ⟨u, hu⟩ := tr_exists J (p / p₀)
    have h3 : (p / p₀).1.1 = 1 := by
      change p.1.1.toAdd - p₀.1.1.toAdd = 0
      rw [hp, hp₀, sub_self]
    have h4 := μ.mul _ _ _ _ _ h1 (r_of_tr_zero μ J hB hG h3 hu)
    have h5 := tr_mul J ha₀ hu
    rw [mul_div_cancel] at h4 h5
    rw [tr_unique J ha h5, mul_right_comm, ← e]
    exact h4
end GlobalTheory.LabelsAgree
