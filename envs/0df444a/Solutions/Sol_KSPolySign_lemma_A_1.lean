-- Prove2me | solution 1 for KSPolySign.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:56:28.139188+00:00
-- url     : https://prove2.me/submissions/edc915ba-ed25-4766-b52e-5349dc3137c0

import Mathlib
import Definitions.Def_KSPolySign_bernsteinCoeff
open Matrix
open scoped ComplexOrder

namespace KSPolySign.LA1
open KSPolySign

/-- weight -/
noncomputable def bw (N μ : ℕ) (t : ℝ) : ℝ := (N.choose μ : ℝ) * t ^ μ * (1 - t) ^ (N - μ)

theorem pow_eq_sum_bw (N k : ℕ) (hk : k ≤ N) (t : ℝ) :
    t ^ k = ∑ μ ∈ Finset.range (N + 1), ((μ.choose k : ℝ) / (N.choose k : ℝ)) * bw N μ t := by
  have hNk : (N.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hsplit : N + 1 = k + (N - k + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range k, ((x.choose k : ℝ) / (N.choose k : ℝ)) * bw N x t = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    simp [Nat.choose_eq_zero_of_lt hx]
  rw [h0, zero_add]
  have : ∀ i ∈ Finset.range (N - k + 1),
      (((k + i).choose k : ℝ) / (N.choose k : ℝ)) * bw N (k + i) t =
        t ^ k * (t ^ i * (1 - t) ^ (N - k - i) * ((N - k).choose i : ℝ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hc := Nat.choose_mul (n := N) (k := k + i) (s := k) (by omega)
    unfold bw
    have hc' : (N.choose (k + i) : ℝ) * ((k + i).choose k : ℝ) =
        (N.choose k : ℝ) * ((N - k).choose i : ℝ) := by
      rw [show k + i - k = i by omega] at hc
      exact_mod_cast hc
    rw [show N - (k + i) = N - k - i by omega, pow_add]
    field_simp
    linear_combination t ^ k * t ^ i * (1 - t) ^ (N - k - i) * hc'
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← add_pow]
  simp

theorem bw_sum (N : ℕ) (t : ℝ) : ∑ μ ∈ Finset.range (N + 1), bw N μ t = 1 := by
  have := add_pow t (1 - t) N
  rw [add_sub_cancel, one_pow] at this
  rw [this]
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold bw; ring

theorem bw_nonneg (N μ : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ bw N μ t := by
  unfold bw
  have : 0 ≤ 1 - t := by linarith
  positivity

theorem lemma_A_1 (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (a b : Fin d → ℝ) (hab : ∀ j, a j < b j)
    (N : Fin d → ℕ)
    (hN : ∀ ν ∈ (MvPolynomial.bind₁ (fun j => MvPolynomial.C (a j) +
        MvPolynomial.C (b j - a j) * MvPolynomial.X j) P).support, ∀ j, ν j ≤ N j)
    (x : Fin d → ℝ) (hx : ∀ j, a j ≤ x j ∧ x j ≤ b j) :
    (∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ bernsteinCoeff P a b N μ ≤ MvPolynomial.eval x P) ∧
    ∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ MvPolynomial.eval x P ≤ bernsteinCoeff P a b N μ := by
  set Q := MvPolynomial.bind₁ (fun j => MvPolynomial.C (a j) +
        MvPolynomial.C (b j - a j) * MvPolynomial.X j) P with hQ
  set u : Fin d → ℝ := fun j => (x j - a j) / (b j - a j) with hu
  have hba : ∀ j, 0 < b j - a j := fun j => sub_pos.mpr (hab j)
  have hu0 : ∀ j, 0 ≤ u j := fun j => div_nonneg (by linarith [(hx j).1]) (hba j).le
  have hu1 : ∀ j, u j ≤ 1 := fun j => (div_le_one (hba j)).mpr (by linarith [(hx j).2])
  have hevalPQ : MvPolynomial.eval x P = MvPolynomial.eval u Q := by
    show MvPolynomial.aeval x P = MvPolynomial.aeval u Q
    rw [hQ, MvPolynomial.aeval_bind₁]
    congr 2
    funext j
    simp only [map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hu,
      Algebra.algebraMap_self, RingHom.id_apply]
    field_simp [(hba j).ne']
    ring
  set S := Fintype.piFinset (fun j : Fin d => Finset.range (N j + 1)) with hS
  set W : (Fin d → ℕ) → ℝ := fun μ => ∏ j, bw (N j) (μ j) (u j) with hW
  have hexp : MvPolynomial.eval u Q = ∑ μ ∈ S, bernsteinCoeff P a b N μ * W μ := by
    rw [MvPolynomial.eval_eq']
    have h1 : ∀ ν ∈ Q.support, Q.coeff ν * ∏ j, u j ^ ν j =
        ∑ μ ∈ S, Q.coeff ν * (∏ j, ((μ j).choose (ν j) : ℝ) / ((N j).choose (ν j) : ℝ)) * W μ := by
      intro ν hν
      have : ∏ j, u j ^ ν j = ∏ j, ∑ μj ∈ Finset.range (N j + 1),
          (((μj.choose (ν j) : ℝ) / ((N j).choose (ν j) : ℝ)) * bw (N j) μj (u j)) :=
        Finset.prod_congr rfl fun j _ => pow_eq_sum_bw (N j) (ν j) (hN ν hν j) (u j)
      rw [this, Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.prod_mul_distrib, hW]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    unfold bernsteinCoeff
    rw [← hQ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Nat.choose_eq_zero_of_lt hj]), mul_zero]
  have hW0 : ∀ μ, 0 ≤ W μ := fun μ => Finset.prod_nonneg fun j _ => bw_nonneg _ _ (hu0 j) (hu1 j)
  have hW1 : ∑ μ ∈ S, W μ = 1 := by
    rw [hS, hW, ← Finset.prod_univ_sum (t := fun j => Finset.range (N j + 1))
      (f := fun j μj => bw (N j) μj (u j))]
    exact Finset.prod_eq_one fun j _ => bw_sum _ _
  have hSne : S.Nonempty := ⟨fun _ => 0, by simp [hS]⟩
  have hmem : ∀ μ ∈ S, ∀ j, μ j ≤ N j := by
    intro μ hμ j
    rw [hS, Fintype.mem_piFinset] at hμ
    have := hμ j
    rw [Finset.mem_range] at this
    omega
  rw [hevalPQ, hexp]
  constructor
  · obtain ⟨μ, hμS, hμmin⟩ := Finset.exists_min_image S (bernsteinCoeff P a b N) hSne
    refine ⟨μ, hmem μ hμS, ?_⟩
    calc bernsteinCoeff P a b N μ = ∑ ν ∈ S, bernsteinCoeff P a b N μ * W ν := by
          rw [← Finset.mul_sum, hW1, mul_one]
      _ ≤ ∑ ν ∈ S, bernsteinCoeff P a b N ν * W ν :=
          Finset.sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right (hμmin ν hν) (hW0 ν)
  · obtain ⟨μ, hμS, hμmax⟩ := Finset.exists_max_image S (bernsteinCoeff P a b N) hSne
    refine ⟨μ, hmem μ hμS, ?_⟩
    calc ∑ ν ∈ S, bernsteinCoeff P a b N ν * W ν ≤ ∑ ν ∈ S, bernsteinCoeff P a b N μ * W ν :=
          Finset.sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right (hμmax ν hν) (hW0 ν)
      _ = bernsteinCoeff P a b N μ := by rw [← Finset.mul_sum, hW1, mul_one]

end KSPolySign.LA1

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (a b : Fin d → ℝ) (hab : ∀ j, a j < b j)
    (N : Fin d → ℕ)
    (hN : ∀ ν ∈ (MvPolynomial.bind₁ (fun j => MvPolynomial.C (a j) +
        MvPolynomial.C (b j - a j) * MvPolynomial.X j) P).support, ∀ j, ν j ≤ N j)
    (x : Fin d → ℝ) (hx : ∀ j, a j ≤ x j ∧ x j ≤ b j) :
    (∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ bernsteinCoeff P a b N μ ≤ MvPolynomial.eval x P) ∧
    ∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ MvPolynomial.eval x P ≤ bernsteinCoeff P a b N μ := by
  apply KSPolySign.LA1.lemma_A_1 <;> assumption
