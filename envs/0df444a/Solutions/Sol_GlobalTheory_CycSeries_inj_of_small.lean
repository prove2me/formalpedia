-- Prove2me | solution 1 for GlobalTheory.CycSeries.inj_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:22:24.57237+00:00
-- url     : https://prove2.me/submissions/71913cb9-5def-4f1c-b59a-9bfd15588dbf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Theorems.Thm_GlobalTheory_CycSeries_mulVec_mem

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
variable {C : Type} [NormedField C]
namespace GlobalTheory.CycSeries
theorem _root_.solution {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p q : C) (hp : p ≠ 0) (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (hgq : g q = q)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ x ∈ X, S (p * q * x) = p * q * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) : y = 0 := by
  have key : ∀ n : ℕ, ∀ y : Fin r → C, (∀ a, y a ∈ X) →
      (∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) → ∀ a, ‖y a‖ ≤ ‖q‖ ^ n := by
    intro n
    induction n with
    | zero => intro y hy _ a; simpa using hX1 _ (hy a)
    | succ n ih =>
      intro y hy h a
      have hm : ∀ a, -B.mulVec (fun b => g (y b)) a ∈ X := fun a =>
        X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hy b)) a)
      let z : Fin r → C := fun a => S (-B.mulVec (fun b => g (y b)) a)
      have hyz : ∀ a, y a = q * z a := fun a => by
        apply mul_left_cancel₀ hp
        rw [← (hS _ (hy a)).2, eq_neg_of_add_eq_zero_left (h a), ← mul_neg, hlin _ (hm a), mul_assoc]
      have := ih z (fun a => (hS _ (hm a)).1) (fun a => by
        apply mul_left_cancel₀ hq
        have h1 := h a
        have e : (fun b => g (y b)) = q • fun b => g (z b) := by
          funext b; rw [hyz b, map_mul, hgq]; rfl
        rw [e, Matrix.mulVec_smul, hyz a, map_mul, hgq, Pi.smul_apply, smul_eq_mul] at h1
        linear_combination h1) a
      rw [hyz a, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  funext a
  exact norm_le_zero_iff.1 (ge_of_tendsto'
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1) fun n => key n y hy h a)
end GlobalTheory.CycSeries
