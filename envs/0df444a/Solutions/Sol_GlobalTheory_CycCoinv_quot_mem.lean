-- Prove2me | solution 1 for GlobalTheory.CycCoinv.quot_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:19:30.781815+00:00
-- url     : https://prove2.me/submissions/a9c3e546-e4db-44de-be6f-606e02e10a90

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_CycCoinv_root_mem_inC
import Theorems.Thm_GlobalTheory_CycCoinv_norm_l
import Theorems.Thm_GlobalTheory_CycEigen_root_mem_inC
import Theorems.Thm_GlobalTheory_CycSeries_root_mem_inC
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_l
import Theorems.Thm_GlobalTheory_Cyc_norm_primitiveRoot_sub_one
import Theorems.Thm_GlobalTheory_UnramValue_norm_l


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycCoinv
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) {N : ℕ} (hN : 1 ≤ N) :
    (l : PadicComplex l) ^ N / (ζ - 1) ∈ intR (Ks K j) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.1.two_le
  have hz := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  refine ⟨(mem_fld _ _).1 (div_mem (pow_mem (natCast_mem _ _) _)
    (sub_mem ((mem_fld _ _).2 (root_mem_inC K hj h)) (one_mem _))), ?_⟩
  rw [norm_div, div_le_one (norm_pos_iff.2 hz0), norm_pow, norm_l, hz]
  calc ((l : ℝ)⁻¹) ^ N ≤ ((l : ℝ)⁻¹) ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1.le) hN
    _ = (l : ℝ) ^ (-1 : ℝ) := by rw [pow_one, Real.rpow_neg_one]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le h1.le
        simp only [tsub_self, pow_zero, one_mul]
        rw [le_div_iff₀ (by linarith)]
        linarith
end GlobalTheory.CycCoinv
