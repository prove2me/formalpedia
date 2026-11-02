-- Prove2me | solution 1 for NoSignalPA.bernstein_chain
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:46:53.950218+00:00
-- url     : https://prove2.me/submissions/b3be161a-be78-4eab-9046-00994167b864

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_NoSignalPA_uniformExp

namespace NoSignalPABernsteinAux

/-- Markov's inequality for the uniform law on a finite type. -/
lemma uniformProbability_one_le {α : Type} [Fintype α] [Nonempty α] (Y : α → ℝ)
    (hY : ∀ ω, 0 ≤ Y ω) :
    OAI.ThorpCompatibility.uniformProbability (fun ω => 1 ≤ Y ω) ≤
      NoSignalPA.uniformExp Y := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability NoSignalPA.uniformExp
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  apply div_le_div_of_nonneg_right _ hc.le
  calc ((Finset.univ.filter fun ω => 1 ≤ Y ω).card : ℝ)
      = ∑ ω ∈ Finset.univ.filter (fun ω => 1 ≤ Y ω), (1 : ℝ) := by simp
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => 1 ≤ Y ω), Y ω :=
        Finset.sum_le_sum fun ω hω => (Finset.mem_filter.mp hω).2
    _ ≤ ∑ ω, Y ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => hY ω)

/-- Monotonicity of the uniform probability. -/
lemma uniformProbability_mono {α : Type} [Fintype α] (P Q : α → Prop) (h : ∀ ω, P ω → Q ω) :
    OAI.ThorpCompatibility.uniformProbability P ≤ OAI.ThorpCompatibility.uniformProbability Q := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

end NoSignalPABernsteinAux

open NoSignalPABernsteinAux in
theorem solution {Nr Ns : ℕ} (k : NoSignalPA.Str Ns) (μ : NoSignalPA.Str Nr → ℝ) (J β : ℝ)
    (hβ : 0 ≤ β) :
    let V : (NoSignalPA.Str Nr → NoSignalPA.Str Ns) → NoSignalPA.Str Nr → ℝ :=
      fun h a => if h a = k then 1 else 0
    let p : ℝ := ((2 : ℝ) ^ Ns)⁻¹
    OAI.ThorpCompatibility.uniformProbability (fun h => J ≤ ∑ a, μ a * V h a)
        ≤ OAI.ThorpCompatibility.uniformProbability
            (fun h => 1 ≤ Real.exp (-β * J + β * ∑ a, μ a * V h a)) ∧
      OAI.ThorpCompatibility.uniformProbability
          (fun h => 1 ≤ Real.exp (-β * J + β * ∑ a, μ a * V h a))
        ≤ Real.exp (-β * J) * NoSignalPA.uniformExp (fun h => Real.exp (β * ∑ a, μ a * V h a)) ∧
      Real.exp (-β * J) * NoSignalPA.uniformExp (fun h => Real.exp (β * ∑ a, μ a * V h a))
        ≤ Real.exp (-β * J) * ∏ a, (p * Real.exp (β * μ a) + (1 - p)) ∧
      ((∀ a, |β * μ a| ≤ 1) →
        Real.exp (-β * J) * ∏ a, (p * Real.exp (β * μ a) + (1 - p))
          ≤ Real.exp (-β * J) * ∏ a, (1 + p * (β * μ a + β ^ 2 * μ a ^ 2))) ∧
      Real.exp (-β * J) * ∏ a, (1 + p * (β * μ a + β ^ 2 * μ a ^ 2))
        ≤ Real.exp (-β * J + p * ∑ a, (β * μ a + β ^ 2 * μ a ^ 2)) := by
  intro V p
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    simp only [p]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hE := Real.exp_pos (-β * J)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `J ≤ X` implies `1 ≤ exp(β (X - J))`
    refine uniformProbability_mono _ _ fun h hJ => ?_
    apply Real.one_le_exp
    nlinarith
  · -- (2) Markov
    have := uniformProbability_one_le (fun h => Real.exp (-β * J + β * ∑ a, μ a * V h a))
      (fun h => (Real.exp_pos _).le)
    refine this.trans (le_of_eq ?_)
    unfold NoSignalPA.uniformExp
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Real.exp_add]
  · -- (3) independence of the values of a uniformly random function
    apply le_of_eq
    congr 1
    unfold NoSignalPA.uniformExp
    have hexp : ∀ h : NoSignalPA.Str Nr → NoSignalPA.Str Ns,
        Real.exp (β * ∑ a, μ a * V h a) = ∏ a, (if h a = k then Real.exp (β * μ a) else 1) := by
      intro h
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [V]
      split_ifs <;> simp
    simp only [hexp]
    rw [← Fintype.prod_sum (fun a v => if v = k then Real.exp (β * μ a) else 1)]
    have hsum : ∀ a, ∑ v : NoSignalPA.Str Ns, (if v = k then Real.exp (β * μ a) else 1) =
        Real.exp (β * μ a) + ((2 : ℝ) ^ Ns - 1) := by
      intro a
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_eq',
        if_pos (Finset.mem_univ k), Finset.card_singleton, one_smul, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast [Nat.one_le_two_pow]
      ring
    simp only [hsum]
    have hcard : ((Fintype.card (NoSignalPA.Str Nr → NoSignalPA.Str Ns) : ℕ) : ℝ) =
        ∏ _a : NoSignalPA.Str Nr, (2 : ℝ) ^ Ns := by
      rw [Finset.prod_const, Finset.card_univ]
      simp [NoSignalPA.Str, Fintype.card_bool, Fintype.card_fin]
    rw [hcard, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [p]
    have h2 : (2 : ℝ) ^ Ns ≠ 0 := by positivity
    field_simp
  · -- (4) `e^x ≤ 1 + x + x²` for `|x| ≤ 1`
    intro hsmall
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply Finset.prod_le_prod
    · intro a _
      have := Real.exp_pos (β * μ a)
      nlinarith
    · intro a _
      have hb := Real.abs_exp_sub_one_sub_id_le (hsmall a)
      have hb' := (abs_le.mp hb).2
      have : Real.exp (β * μ a) ≤ 1 + β * μ a + β ^ 2 * μ a ^ 2 := by nlinarith
      nlinarith
  · -- (5) `1 + t ≤ e^t`
    rw [Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hE.le
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro a _
      have hq : -(1 / 4 : ℝ) ≤ β * μ a + β ^ 2 * μ a ^ 2 := by nlinarith [sq_nonneg (β * μ a + 1 / 2)]
      nlinarith
    · intro a _
      have := Real.add_one_le_exp (p * (β * μ a + β ^ 2 * μ a ^ 2))
      linarith
