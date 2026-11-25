-- Prove2me | solution 1 for GlobalTheory.CycPerturb.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:28:23.228191+00:00
-- url     : https://prove2.me/submissions/fdac4160-ddef-4c32-917c-5ec9cb563e14

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_mem_inC_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution {F : IntermediateField ℚ_[l] (Om l)} {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (hB : ∀ a b, ‖B a b‖ < 1)
    (hBO : ∀ a b, B a b ∈ intC F) :
    ∃ (π : PadicComplex l) (B' : Matrix (Fin r) (Fin r) (PadicComplex l)), π ∈ intC F ∧ ‖π‖ < 1 ∧
      (∀ a b, B' a b ∈ intC F) ∧ B = π • B' := by
  have h0 : (0 : PadicComplex l) ∈ intC F := ⟨(mem_inC_iff _ _).2 (zero_mem _), by simp⟩
  by_cases hz : B = 0
  · exact ⟨0, 0, h0, by simp, fun a b => h0, by simp [hz]⟩
  obtain ⟨a₀, b₀, hne⟩ : ∃ a b, B a b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (Matrix.ext hcon)
  haveI : Nonempty (Fin r × Fin r) := ⟨(a₀, b₀)⟩
  obtain ⟨q, hq⟩ := Finite.exists_max fun q : Fin r × Fin r => ‖B q.1 q.2‖
  have hpos : 0 < ‖B q.1 q.2‖ := (norm_pos_iff.2 hne).trans_le (hq (a₀, b₀))
  have hq0 : B q.1 q.2 ≠ 0 := norm_pos_iff.1 hpos
  refine ⟨B q.1 q.2, (B q.1 q.2)⁻¹ • B, hBO _ _, hB _ _, fun a b => ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, mem_inC_iff]
    exact mul_mem (inv_mem ((mem_inC_iff _ _).1 (hBO _ _).1)) ((mem_inC_iff _ _).1 (hBO _ _).1)
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hq (a, b)
  · rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]
end GlobalTheory.CycPerturb
