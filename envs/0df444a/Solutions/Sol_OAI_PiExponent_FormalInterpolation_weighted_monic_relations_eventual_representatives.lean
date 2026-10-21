-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_monic_relations_eventual_representatives
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:26:57.705444+00:00
-- url     : https://prove2.me/submissions/18ccaf08-acd8-4f7f-9736-2143997c01f7

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_WeightedDivision_positive_weight_wellFounded
import Theorems.Thm_OAI_PiExponent_WeightedDivision_power_monic_relation
import Theorems.Thm_OAI_PiExponent_WeightedDivision_remainder_of_wellFounded_relations

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (k : Nat) (hk : 0 < k)
    (b : Fin d → Nat) (hb : ∀ i, 0 < b i)
    (F : Fin d → MvPolynomial (Fin d) Complex)
    (hF : ∀ i, F i ∈ I ^ k)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real))
    (a delta : Rat) (ha0 : 0 < a) (ha : a < delta)
    (hbudget : ∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) :
    ∃ n₀ : Nat, ∀ n : Nat, n₀ ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ u ∈ q.support,
            ∑ i, (w i : Real) * (u i : Real) ≤ (n : Real) * (delta : Real) := by
  classical
  let wv : Fin d → ℝ := fun i => (w i : ℝ)
  have hwv : ∀ i, 0 < wv i := fun i => hw i
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hδaR : (a : ℝ) < (delta : ℝ) := by exact_mod_cast ha
  have hδsub : (0 : ℝ) < (delta : ℝ) - (a : ℝ) := sub_pos.mpr hδaR
  let C : ℝ := ∑ i, wv i * (((b i - 1 : ℕ)) : ℝ)
  have hCnn : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hwv i)) (Nat.cast_nonneg _)
  let W : (Fin d →₀ ℕ) → ℝ := fun u => ∑ i, wv i * (u i : ℝ)
  let r : (Fin d →₀ ℕ) → (Fin d →₀ ℕ) → Prop := fun u v => W u < W v
  have hwf : WellFounded r := by
    have h := OAI.PiExponent.WeightedDivision.positive_weight_wellFounded wv hwv
    simpa [r, W] using h
  -- threshold
  refine ⟨⌈C / ((delta : ℝ) - (a : ℝ))⌉₊ + 1, ?_⟩
  intro n hn p
  have hnC : C ≤ (n : ℝ) * ((delta : ℝ) - (a : ℝ)) := by
    have h1 : C / ((delta : ℝ) - (a : ℝ)) ≤ (⌈C / ((delta : ℝ) - (a : ℝ))⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈C / ((delta : ℝ) - (a : ℝ))⌉₊ : ℝ) ≤ (n : ℝ) := by
      have h3 : (⌈C / ((delta : ℝ) - (a : ℝ))⌉₊ : ℕ) + 1 ≤ n := hn
      have h4 : (⌈C / ((delta : ℝ) - (a : ℝ))⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h3
      linarith
    exact (div_le_iff₀ hδsub).mp (le_trans h1 h2)
  -- termwise bound for the weight of an exponent vector
  have hWbound : ∀ u : Fin d →₀ ℕ,
      W u ≤ (k : ℝ) * (a : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ) + C := by
    intro u
    have hterm : ∀ i, wv i * (u i : ℝ) ≤
        (wv i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ) + wv i * (((b i - 1 : ℕ)) : ℝ) := by
      intro i
      have hmod : u i % b i ≤ b i - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ (hb i))
      have hu_le : u i ≤ b i * (u i / b i) + (b i - 1) := by
        have h := Nat.div_add_mod (u i) (b i)
        omega
      have hcast : (u i : ℝ) ≤ (b i : ℝ) * ((u i / b i : ℕ) : ℝ) + (((b i - 1 : ℕ)) : ℝ) := by
        exact_mod_cast hu_le
      calc wv i * (u i : ℝ)
          ≤ wv i * ((b i : ℝ) * ((u i / b i : ℕ) : ℝ) + (((b i - 1 : ℕ)) : ℝ)) :=
            mul_le_mul_of_nonneg_left hcast (le_of_lt (hwv i))
        _ = (wv i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ) + wv i * (((b i - 1 : ℕ)) : ℝ) := by ring
    calc W u = ∑ i, wv i * (u i : ℝ) := rfl
      _ ≤ ∑ i, ((wv i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ) +
            wv i * (((b i - 1 : ℕ)) : ℝ)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, (wv i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ)) + C := by
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ i, ((k : ℝ) * (a : ℝ)) * ((u i / b i : ℕ) : ℝ)) + C := by
            have hb' : ∀ i ∈ (Finset.univ : Finset (Fin d)),
                (wv i * (b i : ℝ)) * ((u i / b i : ℕ) : ℝ) ≤
                  ((k : ℝ) * (a : ℝ)) * ((u i / b i : ℕ) : ℝ) := by
              intro i _
              exact mul_le_mul_of_nonneg_right (by simpa [wv] using hbudget i) (Nat.cast_nonneg _)
            have hsum := Finset.sum_le_sum hb'
            linarith
      _ = (k : ℝ) * (a : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ) + C := by
            rw [← Finset.mul_sum]
            push_cast
            ring
  -- relation hypothesis
  have hrel : ∀ u, ¬ (W u ≤ (n : ℝ) * (delta : ℝ)) →
      ∃ G : MvPolynomial (Fin d) Complex, G ∈ I ^ n ∧
        ∀ v ∈ (MvPolynomial.monomial u (1 : Complex) - G).support, r v u := by
    intro u hAu
    have hlt : (n : ℝ) * (delta : ℝ) < W u := lt_of_not_ge hAu
    by_cases hcase : k * (∑ i, u i / b i) < n
    · exfalso
      have hnn : 1 ≤ n := by omega
      have hks : k * (∑ i, u i / b i) ≤ n - 1 := Nat.le_pred_of_lt hcase
      have hksR : ((∑ i, u i / b i : ℕ) : ℝ) * (k : ℝ) ≤ (((n - 1 : ℕ)) : ℝ) := by
        have h := hks
        calc ((∑ i, u i / b i : ℕ) : ℝ) * (k : ℝ)
            = ((k * (∑ i, u i / b i) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (((n - 1 : ℕ)) : ℝ) := by exact_mod_cast h
      have hs_le : ((∑ i, u i / b i : ℕ) : ℝ) ≤ (((n - 1 : ℕ)) : ℝ) / (k : ℝ) :=
        (le_div_iff₀ hkR).mpr hksR
      have hW1 := hWbound u
      have hka : (k : ℝ) * (a : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ) ≤
          (a : ℝ) * (((n - 1 : ℕ)) : ℝ) := by
        calc (k : ℝ) * (a : ℝ) * ((∑ i, u i / b i : ℕ) : ℝ)
            ≤ (k : ℝ) * (a : ℝ) * ((((n - 1 : ℕ)) : ℝ) / (k : ℝ)) := by
              have h1 : (0 : ℝ) ≤ (k : ℝ) * (a : ℝ) := le_of_lt (mul_pos hkR haR)
              exact mul_le_mul_of_nonneg_left hs_le h1
          _ = (a : ℝ) * (((n - 1 : ℕ)) : ℝ) := by field_simp
      have hcast1 : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hnn]; simp
      have hW2 : W u ≤ (n : ℝ) * (delta : ℝ) := by
        have : (a : ℝ) * (((n - 1 : ℕ)) : ℝ) + C ≤ (n : ℝ) * (delta : ℝ) := by
          rw [hcast1]
          nlinarith [hnC]
        linarith
      exact absurd hW2 hAu
    · have hksge : n ≤ k * (∑ i, u i / b i) := le_of_not_gt hcase
      have hbelow' : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, wv j * (v j : ℝ)) < wv i * (b i : ℝ) := by
        intro i v hv
        have := hbelow i v hv
        simpa [wv] using this
      obtain ⟨G, hGmem, hGbelow⟩ := OAI.PiExponent.WeightedDivision.power_monic_relation
        wv b hb F hbelow' (∑ i, u i / b i) u le_rfl
      have hspan_le : Ideal.span (Set.range F) ≤ I ^ k := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hF i
      have hmono : ∀ s : ℕ, (Ideal.span (Set.range F)) ^ s ≤ (I ^ k) ^ s := by
        intro s
        induction s with
        | zero => simp
        | succ m ih =>
            rw [pow_succ, pow_succ]
            exact Ideal.mul_mono ih hspan_le
      have hG' : G ∈ (I ^ k) ^ (∑ i, u i / b i) := hmono _ hGmem
      have hG'' : G ∈ I ^ (k * (∑ i, u i / b i)) := by
        rwa [show (I ^ k) ^ (∑ i, u i / b i) = I ^ (k * (∑ i, u i / b i)) from
          (pow_mul I k (∑ i, u i / b i)).symm] at hG'
      refine ⟨G, Ideal.pow_le_pow_right hksge hG'', ?_⟩
      intro v hv
      have := hGbelow v hv
      simpa [r, W] using this
  exact OAI.PiExponent.WeightedDivision.remainder_of_wellFounded_relations r hwf (I ^ n)
    (fun u => W u ≤ (n : ℝ) * (delta : ℝ)) hrel p
