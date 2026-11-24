-- Prove2me | solution 1 for GlobalTheory.HeckeLocInt.inv_mul_int_of_left_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:12.856675+00:00
-- url     : https://prove2.me/submissions/8b673f22-64d1-4b99-8a98-ec100e183c05

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral
import Theorems.Thm_GlobalTheory_HeckeLocInt_le_exp_neg_one_of_lt
import Theorems.Thm_GlobalTheory_HeckeLocInt_int_mul
import Theorems.Thm_GlobalTheory_HeckeLocInt_small_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.HeckeLocInt
open Matrix
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.HeckeLocInt
theorem _root_.solution {n : ℕ} (ϖ : K) (k : ℕ)
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a a' b b' g g' : GL (Fin n) K)
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hsub : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) K) i j -
      (a' : Matrix (Fin n) (Fin n) K) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K))
    (hg' : (g' : Matrix (Fin n) (Fin n) K) =
      (a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hDD : Formalism.UG.diagJ n ϖ⁻¹ k * Formalism.UG.diagJ n ϖ k = 1 := by
    unfold Formalism.UG.diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ0]
  have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hg]
    have e : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K)) =
        ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K)) *
        Formalism.UG.diagJ n ϖ k) * (b : Matrix (Fin n) (Fin n) K) := by
      simp only [Matrix.mul_assoc]
    rw [e, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul]
  have key : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) * (b' : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD,
      add_sub_cancel]
    simp only [Matrix.mul_assoc]
  have hsub' : ∀ i j, Valued.v (((a' : Matrix (Fin n) (Fin n) K) -
      (a : Matrix (Fin n) (Fin n) K)) i j) < 1 := by
    intro i j; rw [Matrix.sub_apply, Valuation.map_sub_swap]; exact hsub i j
  have hN := small_mul hai hsub'
  have hX : ∀ i j, Valued.v ((1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) i j) ≤ 1 := by
    intro i j
    rw [Matrix.add_apply]
    apply Valuation.map_add_le
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · simp only [Formalism.UG.diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [map_mul, map_mul]
      have h1 : Valued.v (if (i : ℕ) < k then ϖ⁻¹ else 1) ≤ WithZero.exp (1 : ℤ) := by
        split_ifs
        · rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
        · rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
      have h2 : Valued.v (if (j : ℕ) < k then ϖ else 1) ≤ 1 := by
        split_ifs
        · rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
        · rw [map_one]
      have h3 := le_exp_neg_one_of_lt (hN i j)
      calc _ ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' h1 h3) h2
        _ = 1 := by rw [mul_one, ← WithZero.exp_add]; simp
  rw [Units.val_mul, hinv, hg', key]
  exact int_mul (int_mul hbi hX) hb'
end GlobalTheory.HeckeLocInt
