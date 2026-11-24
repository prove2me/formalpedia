-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.Tm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:51:38.487947+00:00
-- url     : https://prove2.me/submissions/86fed715-f039-459d-bfac-9de57bc6c4c1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (h : Q * P = 1) (x : ℂ) (a b : Fin n) :
    Tm (fun (a b : Fin n) ↦ ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) x a b =
      ∑ d, Q b d • ∑ c, P c a • Tm E x c d := by
  have h1 : ∑ d, Q b d * P d a = if a = b then 1 else 0 := by
    have := congrFun (congrFun h b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]; simp [eq_comm]
  simp only [Tm, smul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul,
      ← Finset.sum_smul, h1]
    split_ifs <;> simp
  · rw [Finset.sum_comm]
    simp only [Finset.smul_sum, smul_smul, mul_comm]
end GlobalTheory.QuantumMinorAdjacentSwap
