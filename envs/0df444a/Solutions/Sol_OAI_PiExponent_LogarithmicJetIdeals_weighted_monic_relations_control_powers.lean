-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_monic_relations_control_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-19T03:10:04.411968+00:00
-- url     : https://prove2.me/submissions/65e6c17d-a9e6-4115-b2b5-9f17a8297771

import Theorems.Thm_OAI_PiExponent_weighted_monic_staircase_remainder
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem weighted_block_count_bound
    {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (k n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hsize : ∀ i, d i * (b i : ℝ) ≤ (k : ℝ) * a)
    (u : ι → ℕ) (hcount : k * (∑ i, u i / b i) ≤ n) :
    (∑ i, d i * (u i : ℝ)) ≤
      (n : ℝ) * a + ∑ i, d i * ((b i - 1 : ℕ) : ℝ) := by
  have hterm (i : ι) :
      d i * (u i : ℝ) ≤
        ((u i / b i : ℕ) : ℝ) * ((k : ℝ) * a) +
          d i * ((b i - 1 : ℕ) : ℝ) := by
    have hrNat : u i % b i ≤ b i - 1 := by
      have hr := Nat.mod_lt (u i) (hb i)
      omega
    have hr : ((u i % b i : ℕ) : ℝ) ≤ ((b i - 1 : ℕ) : ℝ) := by
      exact (Nat.cast_le (α := ℝ)).mpr hrNat
    have heq : (u i : ℝ) =
        ((u i % b i : ℕ) : ℝ) +
          (b i : ℝ) * ((u i / b i : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using
        congrArg (fun t : ℕ => (t : ℝ)) (Nat.mod_add_div (u i) (b i)).symm
    calc
      d i * (u i : ℝ) =
          d i * ((u i % b i : ℕ) : ℝ) +
            (d i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ) := by
        rw [heq]
        ring
      _ ≤ d i * ((b i - 1 : ℕ) : ℝ) +
            ((k : ℝ) * a) * ((u i / b i : ℕ) : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hr (hd i))
          (mul_le_mul_of_nonneg_right (hsize i) (Nat.cast_nonneg _))
      _ = _ := by ring
  have hc : (k : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ) ≤ (n : ℝ) := by
    simpa only [Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hcount
  calc
    (∑ i, d i * (u i : ℝ)) ≤
        ∑ i, (((u i / b i : ℕ) : ℝ) * ((k : ℝ) * a) +
          d i * ((b i - 1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((∑ i, u i / b i : ℕ) : ℝ) * ((k : ℝ) * a) +
          ∑ i, d i * ((b i - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Nat.cast_sum]
    _ = ((k : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ)) * a +
          ∑ i, d i * ((b i - 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc ha) le_rfl

theorem solution
    {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (k : ℕ) (hk : 0 < k)
    (b : Fin (m + 1) → ℕ) (hb : ∀ i, 0 < b i)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hF : ∀ i, F i ∈ I ^ k)
    (hbelow : ∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, InterpolationMatrix.columnWeights w0 w j * (u j : ℝ)) <
        InterpolationMatrix.columnWeights w0 w i * (b i : ℝ))
    (a : ℝ) (ha : 0 < a)
    (hsize : ∀ i, InterpolationMatrix.columnWeights w0 w i * (b i : ℝ) ≤
      (k : ℝ) * a) :
    ∀ n : ℕ, ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : WeightedPolynomial w0 w
          ((n : ℝ) * a +
            ∑ i, InterpolationMatrix.columnWeights w0 w i * ((b i - 1 : ℕ) : ℝ)),
        P - Q.val ∈ I ^ n := by
  intro n P
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨⟨0, ?_⟩, ?_⟩
    · intro u hu
      simp at hu
    · simp [Ideal.one_eq_top]
  let s : ℕ := (n - 1) / k + 1
  obtain ⟨Q, hmem, hsupport⟩ :=
    OAI.PiExponent.weighted_monic_staircase_remainder
      (InterpolationMatrix.columnWeights w0 w) hw b hb F hbelow s P
  have hJ : Ideal.span (Set.range F) ≤ I ^ k := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hF i
  have hns : n ≤ k * s := by
    have hdiv : (n - 1) / k < s := by
      dsimp [s]
      omega
    have hlt : n - 1 < s * k := (Nat.div_lt_iff_lt_mul hk).mp hdiv
    rw [Nat.mul_comm]
    omega
  refine ⟨⟨Q, ?_⟩, ?_⟩
  · intro u hu
    have hquot : (∑ i, u i / b i) ≤ (n - 1) / k := by
      have hs := hsupport u hu
      dsimp [s] at hs
      omega
    have hcount : k * (∑ i, u i / b i) ≤ n := by
      calc
        k * (∑ i, u i / b i) ≤ k * ((n - 1) / k) :=
          Nat.mul_le_mul_left k hquot
        _ ≤ n - 1 := by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) k
        _ ≤ n := Nat.sub_le n 1
    exact weighted_block_count_bound
      (InterpolationMatrix.columnWeights w0 w) (fun i => (hw i).le)
      b hb k n a ha.le hsize (fun i => u i) hcount
  · have hmem' : P - Q ∈ (I ^ k) ^ s :=
      (Ideal.pow_right_mono hJ s) hmem
    have hmem'' : P - Q ∈ I ^ (k * s) := by
      simpa only [pow_mul] using hmem'
    exact (Ideal.pow_le_pow_right hns) hmem''
