-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.blockDiagPart_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:33.818794+00:00
-- url     : https://prove2.me/submissions/e0198be7-74e4-4b77-a487-c97178b3cee4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [if_neg (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [if_neg hl, zero_mul]
end GlobalTheory.SatakeWeyl
