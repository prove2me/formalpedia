-- Prove2me | solution 1 for MLManagesComplexity.theorem_6_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:17.080923+00:00
-- url     : https://prove2.me/submissions/876011ff-ccba-48e6-8e42-2eae50011235
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy
import Definitions.Def_MLManagesComplexity_IsCryptoPRG
import Theorems.Thm_MLManagesComplexity_theorem_6_1
import Theorems.Thm_MLManagesComplexity_kl_from_uniform
import Theorems.Thm_MLManagesComplexity_kl_hypothesis_rearrangement

set_option autoImplicit false

open AutoregressiveCompression.Main MLManagesComplexity

private lemma crossEntropy_eq_expectation_logLoss {μ : DistFamily} (hmax : PolyMaxEntropy μ)
    (n : ℕ) (P : PMF (Fin n → Bool)) :
    crossEntropy P (μ n) = ((expectation P (logLoss μ n) : ℝ) : EReal) := by
  obtain ⟨k, hk⟩ := hmax
  have hμ_ne : ∀ x : Fin n → Bool, μ n x ≠ 0 := by
    intro x hzero
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(((n : ℝ) + 2) ^ k)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hle := hk n x
    simp [mass, hzero] at hle
    linarith
  have hno_miss : ¬ ∃ x : Fin n → Bool, P x ≠ 0 ∧ μ n x = 0 := by
    rintro ⟨x, _, hx0⟩
    exact hμ_ne x hx0
  unfold crossEntropy expectation logLoss
  rw [if_neg hno_miss]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hPx : P x = 0
  · simp [mass, hPx]
  · simp [hPx]

theorem solution (ℓ : ℕ → ℕ) (G : (n : ℕ) → (Fin (ℓ n) → Bool) → (Fin n → Bool))
    (hG : IsCryptoPRG ℓ G) (μ : DistFamily) (hμ : PPolyComputable μ) (hmax : PolyMaxEntropy μ)
    (hfit : ∀ n : ℕ, klBits (prgDist ℓ G n) (μ n) ≤ klBits (prgDist ℓ G n) (uniformFamily n)) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n : ℕ, klBits (uniformFamily n) (μ n) ≤ ((ν n : ℝ) : EReal) := by
  obtain ⟨ν, hν_negl, hν_gap⟩ :=
    theorem_6_1 (prgDist ℓ G) uniformFamily hG.2.2 μ hμ hmax
  refine ⟨ν, hν_negl, fun n => ?_⟩
  have hrearr := kl_hypothesis_rearrangement (prgDist ℓ G n) (μ n) (hfit n)
  have hce_le_nat : crossEntropy (prgDist ℓ G n) (μ n) ≤ (n : EReal) := by
    simpa [hrearr.2] using hrearr.1
  rw [crossEntropy_eq_expectation_logLoss hmax n (prgDist ℓ G n)] at hce_le_nat
  have hnat_coe : (n : EReal) = ((n : ℝ) : EReal) := by norm_cast
  rw [hnat_coe] at hce_le_nat
  have hexp_D_le : expectation (prgDist ℓ G n) (logLoss μ n) ≤ (n : ℝ) :=
    EReal.coe_le_coe_iff.mp hce_le_nat
  have hkl_U := kl_from_uniform (n := n) (μ n)
  rw [crossEntropy_eq_expectation_logLoss hmax n (uniformFamily n), hnat_coe,
      ← EReal.coe_sub] at hkl_U
  rw [hkl_U, EReal.coe_le_coe_iff]
  have hgap := (abs_le.mp (hν_gap n)).1
  linarith
