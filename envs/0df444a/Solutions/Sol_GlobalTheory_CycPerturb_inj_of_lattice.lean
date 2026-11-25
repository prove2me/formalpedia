-- Prove2me | solution 1 for GlobalTheory.CycPerturb.inj_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:20.796312+00:00
-- url     : https://prove2.me/submissions/a8f2e393-81a1-4437-bbf7-dfcef47b2c9a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_mulVec_mem

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
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycPerturb
theorem _root_.solution {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p : C) (hp : p ≠ 0) (π : C) (hπ : ‖π‖ < 1) (hgπ : g π = π)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ (k : ℕ), ∀ x ∈ X, S (p * (-π) ^ k * x) = p * (-π) ^ k * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * (π • B).mulVec (fun b => g (y b)) a = 0) : y = 0 := by
  have key : ∀ k : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ ∀ a, y a = (-π) ^ k * z a := by
    intro k
    induction k with
    | zero => exact ⟨y, hy, fun a => by simp⟩
    | succ k ih =>
      obtain ⟨z, hz, hyz⟩ := ih
      have hm : ∀ a, B.mulVec (fun b => g (z b)) a ∈ X :=
        mulVec_mem X B hBX _ (fun b => hgX _ (hz b))
      refine ⟨fun a => S (B.mulVec (fun b => g (z b)) a), fun a => (hS _ (hm a)).1, fun a => ?_⟩
      have e : g (y a) - y a = p * (-π) ^ (k + 1) * B.mulVec (fun b => g (z b)) a := by
        rw [eq_neg_of_add_eq_zero_left (h a)]
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, hyz, map_mul, map_pow,
          map_neg, hgπ, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      have h1 := (hS _ (hy a)).2
      rw [e, hlin _ _ (hm a), mul_assoc] at h1
      exact (mul_left_cancel₀ hp h1).symm
  funext a
  have hle : ∀ k : ℕ, ‖y a‖ ≤ ‖π‖ ^ k := by
    intro k
    obtain ⟨z, hz, hyz⟩ := key k
    rw [hyz, norm_mul, norm_pow, norm_neg]
    exact mul_le_of_le_one_right (by positivity) (hX1 _ (hz a))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ) hle
  exact norm_le_zero_iff.1 this
end GlobalTheory.CycPerturb
