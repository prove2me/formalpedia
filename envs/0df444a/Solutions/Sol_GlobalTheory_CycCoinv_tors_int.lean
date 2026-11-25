-- Prove2me | solution 1 for GlobalTheory.CycCoinv.tors_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:10.645444+00:00
-- url     : https://prove2.me/submissions/f3fc3a18-2276-43ce-99cb-2d3c29f62ce3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_CycCoinv_prod_div

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
namespace GlobalTheory.CycCoinv
theorem _root_.solution {C ι : Type} [Field C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (J : Finset ι) (hJ : aeval U (∏ u ∈ J, (X - Polynomial.C (f u))) = 0)
    (i : ι) (w w' : Fin r → C) (hw : ∀ a, w a ∈ O) (p : C) (hp : p ≠ 0)
    (h : U.mulVec w' - f i • w' = p • w) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      U.mulVec y - f i • y = (∏ u ∈ J.erase i, (f i - f u)) • w := by
  obtain ⟨y, hy, he⟩ := prod_div O U hU (f i) (hf i) f hf w hw (J.erase i)
  have hd : ∏ u ∈ J, (X - Polynomial.C (f u)) ∣
      (∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i)) := by
    by_cases hi : i ∈ J
    · rw [Finset.prod_erase_mul _ _ hi]
    · rw [Finset.erase_eq_of_notMem hi]; exact dvd_mul_right _ _
  obtain ⟨q, hq⟩ := hd
  have h0 : aeval U ((∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i))) = 0 := by
    rw [hq, map_mul, hJ, zero_mul]
  have h1 := congrArg (fun M => Matrix.mulVec M w') h0
  simp only [map_mul, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at h1
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, h, Matrix.mulVec_smul, smul_eq_zero] at h1
  have h2 := h1.resolve_left hp
  rw [h2] at he
  refine ⟨-y, fun a => O.neg_mem (hy a), ?_⟩
  rw [Matrix.mulVec_neg, eq_neg_of_add_eq_zero_left he.symm]
  module
end GlobalTheory.CycCoinv
