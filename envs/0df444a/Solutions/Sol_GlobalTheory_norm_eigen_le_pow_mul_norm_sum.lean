-- Prove2me | solution 1 for GlobalTheory.norm_eigen_le_pow_mul_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:50.819631+00:00
-- url     : https://prove2.me/submissions/d0e6ab4e-59c4-4fd0-811d-377303809adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {H κ : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (lam : κ → ℂ) (s : κ) (Bd : ℝ)
    (hBd : 0 ≤ Bd) (E : Finset κ) :
    (∀ j ∈ E, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ E, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) →
    ∀ v : κ → H, (∀ i, v i ∈ VV ∧ T (v i) = lam i • v i) →
      ‖v s‖ ≤ Bd ^ E.card * ‖v s + ∑ i ∈ E, v i‖ := by
  induction E using Finset.induction_on with
  | empty => intro _ _ v _; simp
  | insert j E hj ih =>
    intro h1 h2 v hv
    have hw : ∀ i, (lam i - lam j) • v i ∈ VV ∧
        T ((lam i - lam j) • v i) = lam i • (lam i - lam j) • v i := fun i =>
      ⟨VV.smul_mem _ (hv i).1, by rw [map_smul, (hv i).2, smul_comm]⟩
    have hih := ih (fun k hk => h1 k (mem_insert_of_mem hk))
      (fun k hk => h2 k (mem_insert_of_mem hk)) (fun i => (lam i - lam j) • v i) hw
    have hy : v s + ∑ i ∈ insert j E, v i ∈ VV :=
      VV.add_mem (hv s).1 (VV.sum_mem fun i _ => (hv i).1)
    have hT := h2 j (mem_insert_self j E) _ hy
    have heq : T (v s + ∑ i ∈ insert j E, v i) - lam j • (v s + ∑ i ∈ insert j E, v i)
        = (lam s - lam j) • v s + ∑ i ∈ E, (lam i - lam j) • v i := by
      rw [sum_insert hj]
      simp only [map_add, map_sum, (hv _).2, smul_add, smul_sum, sub_smul, sum_sub_distrib]
      abel
    rw [heq] at hT
    have hs : ‖v s‖ ≤ ‖(lam s - lam j) • v s‖ := by
      rw [norm_smul]
      exact le_mul_of_one_le_left (norm_nonneg _) (h1 j (mem_insert_self j E))
    rw [card_insert_of_notMem hj, pow_succ, mul_assoc]
    exact hs.trans (hih.trans (mul_le_mul_of_nonneg_left hT (pow_nonneg hBd _)))
end GlobalTheory
