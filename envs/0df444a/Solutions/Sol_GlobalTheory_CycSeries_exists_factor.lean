-- Prove2me | solution 1 for GlobalTheory.CycSeries.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:25.680801+00:00
-- url     : https://prove2.me/submissions/47395ba3-7d8e-40f6-b4be-b1785cc29172

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Theorems.Thm_GlobalTheory_CycSeries_mem_inC_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycSeries
theorem _root_.solution {F : IntermediateField ℚ_[l] (Om l)} {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (h1 : ∀ a b, ‖B a b‖ < 1)
    (hB : ∀ a b, B a b ∈ intC F) :
    ∃ (q : PadicComplex l) (B' : Matrix (Fin r) (Fin r) (PadicComplex l)), q ≠ 0 ∧ ‖q‖ < 1 ∧
      q ∈ intC F ∧ (∀ a b, B' a b ∈ intC F) ∧ B = q • B' := by
  have hq : ∃ q : PadicComplex l, q ≠ 0 ∧ ‖q‖ < 1 ∧ q ∈ inC F ∧ ∀ a b, ‖B a b‖ ≤ ‖q‖ := by
    by_cases h0 : B = 0
    · refine ⟨l, Nat.cast_ne_zero.2 hl.1.ne_zero, ?_, (mem_inC_iff _ _).2 (natCast_mem _ _),
        fun a b => by simp [h0]⟩
      rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.1.one_lt)
    · obtain ⟨a0, b0, hab⟩ : ∃ a b, B a b ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Matrix.ext hc)
      obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r × Fin r))
        (fun s => ‖B s.1 s.2‖) ⟨(a0, b0), Finset.mem_univ _⟩
      refine ⟨B s.1 s.2, ?_, h1 _ _, (hB _ _).1, fun a b => hs (a, b) (Finset.mem_univ _)⟩
      exact norm_pos_iff.1 ((norm_pos_iff.2 hab).trans_le (hs (a0, b0) (Finset.mem_univ _)))
  obtain ⟨q, hq0, hq1, hqF, hq⟩ := hq
  refine ⟨q, q⁻¹ • B, hq0, hq1, ⟨hqF, hq1.le⟩, fun a b => ⟨?_, ?_⟩, ?_⟩
  · exact (mem_inC_iff _ _).2 (mul_mem (inv_mem ((mem_inC_iff _ _).1 hqF))
      ((mem_inC_iff _ _).1 (hB a b).1))
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.2 hq0), mul_one]
    exact hq a b
  · rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]
end GlobalTheory.CycSeries
