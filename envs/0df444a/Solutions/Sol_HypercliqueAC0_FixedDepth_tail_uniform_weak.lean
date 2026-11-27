-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.tail_uniform_weak
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:25:30.258746+00:00
-- url     : https://prove2.me/submissions/f84fefd7-868d-4332-8a19-e39d981cd3b1

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching
import Theorems.Thm_HypercliqueAC0_FixedDepth_restriction_fourier_tail
import Theorems.Thm_HypercliqueAC0_FixedDepth_circuit_collapse
import Theorems.Thm_OAI_Problem313_BiasedFourier_parseval

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- The product weights sum to one. -/
theorem TUW_sum_weight {X : Type} [Fintype X] (p : ℝ) :
    (∑ x : X → Bool, OAI.Problem313.BiasedFourier.weight p x) = 1 := by
  unfold OAI.Problem313.BiasedFourier.weight
  rw [← Fintype.prod_sum (fun (_ : X) (b : Bool) => OAI.Problem313.BiasedFourier.scalarWeight p b)]
  simp [OAI.Problem313.BiasedFourier.scalarWeight]

/-- The Fourier tail of a Boolean function is at most one. -/
theorem TUW_tail_le_one {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (X → Bool) → Bool) (D : ℝ) :
    fourierTailGE p (boolReal f) D ≤ 1 := by
  have hpar := OAI.Problem313.BiasedFourier.parseval hp hp1 (boolReal f)
  unfold fourierTailGE fourierCoeff
  calc (∑ S : Finset X, if D ≤ (S.card : ℝ) then
          (OAI.Problem313.BiasedFourier.coeff p (boolReal f) S) ^ 2 else 0)
      ≤ ∑ S : Finset X, OAI.Problem313.BiasedFourier.coeff p (boolReal f) S ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _
    _ = ∑ x, OAI.Problem313.BiasedFourier.weight p x * (boolReal f x) ^ 2 := hpar
    _ ≤ ∑ x : X → Bool, OAI.Problem313.BiasedFourier.weight p x := by
        apply Finset.sum_le_sum
        intro x _
        have hw : 0 ≤ OAI.Problem313.BiasedFourier.weight p x := by
          unfold OAI.Problem313.BiasedFourier.weight
          apply Finset.prod_nonneg
          intro i _
          unfold OAI.Problem313.BiasedFourier.scalarWeight
          split_ifs <;> linarith
        have hb : (boolReal f x) ^ 2 ≤ 1 := by
          unfold boolReal; split_ifs <;> norm_num
        nlinarith
    _ = 1 := TUW_sum_weight p

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (C : MantriCVQ.ACCircuit X) (w : ℕ),
      C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE (1 / 2) (boolReal C.eval) D ≤
          2 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by
  refine ⟨8 * 32 ^ h, by positivity, ?_⟩
  intro X _ C w hC D hD
  have hG : (0 : ℝ) ≤ C.gates.length := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have := TUW_tail_le_one (p := 1 / 2) (by norm_num) (by norm_num) C.eval D
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    linarith
  · set q : ℝ := (1 / 32) * (1 / (32 * (w : ℝ))) ^ (h - 1) with hq
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hqpos : 0 < q := by positivity
    have hq1 : q ≤ 1 := by
      have : (1 / (32 * (w : ℝ))) ^ (h - 1) ≤ 1 := by
        apply pow_le_one₀ (by positivity)
        rw [div_le_one (by positivity)]; linarith
      rw [hq]; linarith
    have hqK : q * (8 * 32 ^ h * (w : ℝ) ^ h) = 8 * w := by
      obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
      rw [hq, Nat.add_sub_cancel, pow_succ, pow_succ, div_pow, mul_pow]
      field_simp
      simp
    have hDq : 4 * ((w : ℝ) + 1) ≤ q * D := by
      have : q * (8 * 32 ^ h * (w : ℝ) ^ h) ≤ q * D :=
        mul_le_mul_of_nonneg_left (by linarith [hD]) hqpos.le
      nlinarith
    have h1 := restriction_fourier_tail q hqpos hq1 C.eval w D hDq
    have h2 := circuit_collapse h w hh hw C hC
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(w : ℝ)) := by positivity
    calc fourierTailGE (1 / 2) (boolReal C.eval) D
        ≤ 2 * ((C.gates.length : ℝ) * (2 : ℝ) ^ (-(w : ℝ))) := by
          rw [hq] at h1; linarith
      _ ≤ 2 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by nlinarith

