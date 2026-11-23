-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.mem_of_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:05.92595+00:00
-- url     : https://prove2.me/submissions/c0fb3a6c-949d-4051-ae9e-86899b61c27e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {R σ : Type*} [CommRing R] [Finite σ] (N : ℕ)
    (K : Ideal (MvPowerSeries σ R))
    (hK : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : R) : MvPowerSeries σ R) ∈ K)
    (g : MvPowerSeries σ R) (hg : ∀ d : σ →₀ ℕ, d.degree < N → coeff d g = 0) : g ∈ K := by
  classical
  have h1 : ∀ d : σ →₀ ℕ, ∃ α : σ →₀ ℕ, N ≤ d.degree → α ≤ d ∧ α.degree = N := fun d => by
    by_cases hd : N ≤ d.degree
    · obtain ⟨α, h⟩ := Finsupp.exists_le_degree_eq d N hd
      exact ⟨α, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose A hA using h1
  let S := (Finsupp.finite_of_degree_eq (σ := σ) N).toFinset
  have hS : ∀ α, α ∈ S ↔ α.degree = N := fun α => by simp [S]
  let G : (σ →₀ ℕ) → MvPowerSeries σ R := fun α e => if A (α + e) = α then coeff (α + e) g else 0
  have hG : ∀ α e, coeff e (G α) = if A (α + e) = α then coeff (α + e) g else 0 := fun _ _ => rfl
  have : g = ∑ α ∈ S, monomial α 1 * G α := by
    ext d
    simp only [map_sum, coeff_monomial_mul, one_mul, hG]
    by_cases hd : N ≤ d.degree
    · rw [Finset.sum_eq_single_of_mem (A d) ((hS _).2 (hA d hd).2)]
      · simp [(hA d hd).1, add_tsub_cancel_of_le (hA d hd).1]
      · intro α _ hα
        split_ifs with h2 h3
        · rw [add_tsub_cancel_of_le h2] at h3
          exact absurd h3.symm hα
        · rfl
        · rfl
    · rw [hg d (not_le.1 hd)]
      refine (Finset.sum_eq_zero fun α _ => ?_).symm
      split_ifs with h2 h3
      · rw [add_tsub_cancel_of_le h2]
        exact hg d (not_le.1 hd)
      · rfl
      · rfl
  rw [this]
  exact K.sum_mem fun α hα => K.mul_mem_right _ (hK α ((hS α).1 hα))
end GlobalTheory.CompleteBaseChange
