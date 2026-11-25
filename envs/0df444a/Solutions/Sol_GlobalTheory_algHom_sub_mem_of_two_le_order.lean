-- Prove2me | solution 1 for GlobalTheory.algHom_sub_mem_of_two_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:31.344797+00:00
-- url     : https://prove2.me/submissions/41b5c053-9a44-491d-acd5-2eb35c5e5e10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_algHom_mem_pow_of_le_order
import Theorems.Thm_GlobalTheory_algHom_sub_mem_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_eq_sum_X_mul
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X


attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_C

set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J B : Ideal S}
    (hB : B ≤ J) (hφ : ∀ i, φ (X i) ∈ B) (hψ : ∀ i, ψ (X i) ∈ B) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ B * J ^ n) {g : MvPowerSeries σ A} (hg : 2 ≤ g.order) :
    φ g - ψ g ∈ B ^ 2 * J ^ n := by
  cases nonempty_fintype σ
  have key : ∀ g : MvPowerSeries σ A, 1 ≤ g.order → φ g - ψ g ∈ B * J ^ n := by
    intro g hg
    obtain ⟨k, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    have e : φ (X i * k i) - ψ (X i * k i) =
        φ (X i) * (φ (k i) - ψ (k i)) + (φ (X i) - ψ (X i)) * ψ (k i) := by
      simp only [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_mul (hφ i) ?_) (Ideal.mul_mem_right _ _ (h i))
    exact algHom_sub_mem_pow φ ψ (fun i => hB (hφ i)) (fun i => hB (hψ i))
      (fun i => (Ideal.mul_le_inf (I := B) (J := J ^ n) (h i)).2) _
  obtain ⟨k, hk, rfl⟩ := exists_eq_sum_X_mul (n := 1) (g := g) fun d hd =>
    coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)
  have hk' : ∀ i, ((1 : ℕ) : ℕ∞) ≤ (k i).order := fun i => nat_le_order (hk i)
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  have e : φ (X i * k i) - ψ (X i * k i) =
      φ (X i) * (φ (k i) - ψ (k i)) + ψ (k i) * (φ (X i) - ψ (X i)) := by
    simp only [map_mul]; ring
  rw [e, sq, mul_assoc]
  refine add_mem (Ideal.mul_mem_mul (hφ i) (key _ (by exact_mod_cast hk' i)))
    (Ideal.mul_mem_mul ?_ (h i))
  simpa using algHom_mem_pow_of_le_order ψ hψ (hk' i)
end GlobalTheory
