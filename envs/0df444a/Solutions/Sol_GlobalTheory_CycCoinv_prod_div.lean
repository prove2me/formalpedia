-- Prove2me | solution 1 for GlobalTheory.CycCoinv.prod_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:30.9103+00:00
-- url     : https://prove2.me/submissions/ac71c0eb-513f-40a6-a42c-5bcccf2321eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator

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
theorem _root_.solution {C ι : Type} [CommRing C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (b : C) (hb : b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (w : Fin r → C) (hw : ∀ a, w a ∈ O) (s : Finset ι) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      (aeval U (∏ u ∈ s, (X - Polynomial.C (f u)))).mulVec w
        = (∏ u ∈ s, (b - f u)) • w + (U.mulVec y - b • y) := by
  have hmv : ∀ y : Fin r → C, (∀ a, y a ∈ O) → ∀ a, U.mulVec y a ∈ O := fun y hy a => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun c _ => O.mul_mem (hU a c) (hy c)
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a => O.zero_mem, by simp⟩
  | insert u s hu ih =>
    obtain ⟨y, hy, he⟩ := ih
    refine ⟨(∏ u ∈ s, (b - f u)) • w + (U.mulVec y - f u • y), fun a => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact O.add_mem (O.mul_mem (O.prod_mem fun v _ => O.sub_mem hb (hf v)) (hw a))
        (O.sub_mem (hmv y hy a) (O.mul_mem (hf u) (hy a)))
    · rw [Finset.prod_insert hu, Finset.prod_insert hu, map_mul, ← Matrix.mulVec_mulVec, he,
        map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      module
end GlobalTheory.CycCoinv
