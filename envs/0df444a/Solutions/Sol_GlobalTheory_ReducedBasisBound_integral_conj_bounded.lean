-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.integral_conj_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:44:38.182338+00:00
-- url     : https://prove2.me/submissions/ae807ed0-bfdf-4bc3-9b74-8eea715767e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Theorems.Thm_GlobalTheory_ReducedBasisBound_integral_entry_eq_zero
import Theorems.Thm_GlobalTheory_ReducedBasisBound_conj_entry_eq_zero
import Theorems.Thm_GlobalTheory_ReducedBasisBound_entry_bound_of_vanishing
import Theorems.Thm_GlobalTheory_ReducedBasisBound_abs_entry_le_one
import Theorems.Thm_GlobalTheory_ReducedBasisBound_conj_bound
import Theorems.Thm_GlobalTheory_unipotent_upper_inv_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ)
    (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n →
    ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) →
    (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) →
    (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) →
    ∀ i j, |(M i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁ : ℝ, C₁ = max C 1 := ⟨_, rfl⟩
  obtain ⟨Cm0, hCm0⟩ := GlobalTheory.unipotent_upper_inv_bounded N C₁
  obtain ⟨Cm, hCmd⟩ : ∃ Cm : ℝ, Cm = max Cm0 0 := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = N * (N * max R 0) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = N * (Cm * (N * (T * C₁ ^ 3))) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 1 / (K + 1) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / C₁ ^ 2 := ⟨_, rfl⟩
  refine ⟨N * (Cm * (N * (T * C₁ / δ))), ?_⟩
  intro k a n hs X M M' hX hM hM'
  have hC : 1 ≤ C₁ := hC₁d ▸ le_max_right _ _
  have hC₁pos : 0 < C₁ := by linarith
  have hCm : 0 ≤ Cm := hCmd ▸ le_max_right _ _
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hT : 0 ≤ T := by rw [hTd]; positivity
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hε : 0 < ε := by rw [hεd]; positivity
  have hKε : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1 := by
    have e : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) = K * (1 / (K + 1)) := by
      rw [← hεd, hKd]; ring
    rw [e, mul_one_div, div_lt_one (by linarith)]
    linarith
  have hδ : 0 < δ := by rw [hδd]; positivity
  have hδε : δ * C₁ ^ 2 = ε := by rw [hδd]; field_simp
  have hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hs.le i j h).trans
        (mul_le_mul_of_nonneg_right (hC₁d ▸ le_max_left _ _) (hs.pos j).le)
    · subst h
      nlinarith [hs.pos i]
  have hn : ∀ i j, |n i j| ≤ C₁ := fun i j => (hs.bdd i j).trans (hC₁d ▸ le_max_left _ _)
  obtain ⟨m, hmn, hnm, hm_low, hm⟩ := hCm0 n hs.diag hs.lower hn
  have hm' : ∀ i j, |m i j| ≤ Cm := fun i j => (hm i j).trans (hCmd ▸ le_max_left _ _)
  have hk := abs_entry_le_one k hs.orth
  obtain ⟨Z, hZd⟩ : ∃ Z : Matrix (Fin N) (Fin N) ℝ, Z = kᵀ * X * k := ⟨_, rfl⟩
  have hZ : ∀ i j, |Z i j| ≤ T := by
    intro i j
    rw [hZd, hTd]
    exact conj_bound k X hk _ hR (fun i j => (hX i j).trans (le_max_left _ _)) i j
  have h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
  have h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM'
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hA := integral_entry_eq_zero hC hCm hT hs.pos hle hmn hs.lower hm_low hn hm' hZ M' h2 ε hε hKε
  have hB := conj_entry_eq_zero hC hs.pos hle hnm hs.lower hm_low M' h2 ε hA δ hδ.le hδε
  exact entry_bound_of_vanishing hC hCm hT hs.pos hmn hn hm' hZ M h1 δ hδ hB
end GlobalTheory.ReducedBasisBound
