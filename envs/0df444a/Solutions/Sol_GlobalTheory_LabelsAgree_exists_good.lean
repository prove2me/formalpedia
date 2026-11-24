-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:33:06.172801+00:00
-- url     : https://prove2.me/submissions/6a44da71-9070-476d-860a-dd9ae542dcf9

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
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_char_root
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
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
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {n g : ℕ} (hn : (n : C) ≠ 0)
    (hT : N.Tors n g) {j : ℕ} (hj : j ≠ 0) (x : N.X) :
    ∃ p : N.QT ((n ^ j) ^ 2), p.1.1.toAdd = x ∧ ‖N.th (p.1.2.b ^ n ^ j)‖ = 1 := by
  have hn0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by rintro rfl; simp at hn))
  have root : ∀ (i : ℕ) (a : N.A), ∃ b, b ^ n ^ i = a := by
    intro i
    induction i with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨b, rfl⟩ := hT.div a
      obtain ⟨b', rfl⟩ := ih b
      exact ⟨b', by rw [pow_succ, pow_mul]⟩
  obtain ⟨a, ha⟩ := root j (N.c x)
  obtain ⟨t, ht, hth⟩ := hT.good a
  obtain ⟨b, hb⟩ := root j (a * t)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).1 b
  have ht' : t ^ n ^ j = 1 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ', pow_mul, ht, one_pow]
  obtain ⟨u, hu⟩ := (N.exists_tor_iff (N.io x * (γ ^ (n ^ j) ^ 2)⁻¹)).2 (by
    rw [NumD.Gt.mul_b, NumD.Gt.inv_b, NumD.Gt.pow_b, hγ, sq, pow_mul, hb, mul_pow, ht', ha, mul_one, N.io_b,
      mul_inv_cancel])
  obtain ⟨v, hv⟩ := exists_char_root u hn0
  refine ⟨⟨(Multiplicative.ofAdd x, N.tor v * γ), ?_⟩, rfl, ?_⟩
  · rw [N.mem_QT, mul_pow, ← N.tor_pow, hv, hu, inv_mul_cancel_right]
    rfl
  · change ‖N.th ((1 * γ.b) ^ n ^ j)‖ = 1
    rw [one_mul, hγ, hb, hth]
end GlobalTheory.LabelsAgree
