-- Prove2me | solution 1 for LocalLemma.lll_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:27:12.084991+00:00
-- url     : https://prove2.me/submissions/b111f0c1-a52e-44df-9419-9416c5b4fc8b

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_lll
public import Theorems.Thm_LocalLemma_exp_mul_pow_ge_one

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) {p : ℝ} {d : ℕ}
    (hp : ∀ i, μ.real (A i) ≤ p) (hd : ∀ i, Γ.degree i ≤ d)
    (hc : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < μ.real (⋂ i, (A i)ᶜ) := by
  have hd2 : (0:ℝ) < (d:ℝ) + 2 := by positivity
  have hd1 : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have hr : 1 - 1 / ((d:ℝ) + 2) = ((d:ℝ) + 1) / ((d:ℝ) + 2) := by field_simp; ring
  have hr0 : 0 < ((d:ℝ) + 1) / ((d:ℝ) + 2) := by positivity
  have hr1 : ((d:ℝ) + 1) / ((d:ℝ) + 2) ≤ 1 := by rw [div_le_one hd2]; linarith
  have hx1 : ∀ _ : Fin n, 1 / ((d:ℝ) + 2) < 1 := fun _ => by
    rw [div_lt_one hd2]; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  refine lt_of_lt_of_le ?_
    (lll μ A hA Γ hΓ (fun _ => 1 / ((d:ℝ) + 2)) (fun _ => by positivity) hx1 ?_)
  · exact Finset.prod_pos fun i _ => by rw [hr]; exact hr0
  · intro i
    rw [Finset.prod_const, SimpleGraph.card_neighborFinset_eq_degree, hr]
    have hpe : p ≤ 1 / (Real.exp 1 * ((d:ℝ) + 1)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have key := exp_mul_pow_ge_one d
    have hpow : (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ d ≤ (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ Γ.degree i :=
      pow_le_pow_of_le_one hr0.le hr1 (hd i)
    calc μ.real (A i) ≤ p := hp i
      _ ≤ 1 / (Real.exp 1 * ((d:ℝ) + 1)) := hpe
      _ ≤ 1 / ((d:ℝ) + 2) * (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 / ((d:ℝ) + 2) * (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ d * (Real.exp 1 * ((d:ℝ) + 1))
              = Real.exp 1 * (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ (d + 1) := by
            rw [pow_succ]; field_simp
          rw [this]; exact key
      _ ≤ _ := by gcongr
end LocalLemma
