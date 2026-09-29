-- Prove2me | solution 1 for HighDimStat.TailBounds.martingale_bernstein_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:21:28.551552+00:00
-- url     : https://prove2.me/submissions/160fc114-f0ee-4533-a939-6abbb2175fbe

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory

namespace HighDimStat.TailBounds

universe u

/-- Two-step filtration on `ULift Bool`: trivial at time `0`, full afterwards. -/
def aux_mbb_filt : Filtration ℕ (inferInstance : MeasurableSpace (ULift.{u} Bool)) where
  seq := fun k => if k = 0 then ⊥ else inferInstance
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      exact le_rfl

/-- Uniform probability measure on `ULift Bool`. -/
noncomputable def aux_mbb_mu : Measure (ULift.{u} Bool) :=
  (PMF.uniformOfFintype (ULift.{u} Bool)).toMeasure

instance aux_mbb_mu_prob : IsProbabilityMeasure (aux_mbb_mu.{u}) := by
  unfold aux_mbb_mu; infer_instance

/-- The martingale differences: `D 1 = ±2`, all others zero. -/
noncomputable def aux_mbb_D : ℕ → ULift.{u} Bool → ℝ :=
  fun k ω => if k = 1 then (if ω.down then 2 else -2) else 0

/-- The scale parameters: `α 1 = -1` (making the hypotheses vacuous at `k = 1`), else `1`. -/
noncomputable def aux_mbb_α : ℕ → ℝ := fun k => if k = 1 then -1 else 1

lemma aux_mbb_filt_zero : aux_mbb_filt.{u} 0 = ⊥ := by
  simp [aux_mbb_filt]

lemma aux_mbb_filt_pos {k : ℕ} (hk : k ≠ 0) :
    aux_mbb_filt.{u} k = (inferInstance : MeasurableSpace (ULift.{u} Bool)) := by
  simp [aux_mbb_filt, hk]

lemma aux_mbb_real_singleton (b : ULift.{u} Bool) : aux_mbb_mu.real {b} = 1 / 2 := by
  unfold aux_mbb_mu
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  simp

lemma aux_mbb_int_D1 : ∫ ω, aux_mbb_D.{u} 1 ω ∂aux_mbb_mu = 0 := by
  rw [integral_fintype Integrable.of_finite]
  have : (Finset.univ : Finset (ULift.{u} Bool)) = {ULift.up true, ULift.up false} := by
    ext x; cases x with | up b => cases b <;> simp
  rw [this, Finset.sum_pair (by simp)]
  simp [aux_mbb_real_singleton, aux_mbb_D]

lemma aux_mbb_sum (ω : ULift.{u} Bool) :
    ∑ k ∈ Finset.Icc 1 2, aux_mbb_D k ω = aux_mbb_D 1 ω := by
  have : Finset.Icc 1 2 = {1, 2} := by decide
  rw [this, Finset.sum_pair (by norm_num)]
  simp [aux_mbb_D]

lemma aux_mbb_sup (h : (Finset.Icc 1 2).Nonempty) :
    Finset.sup' (Finset.Icc 1 2) h aux_mbb_α = 1 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    unfold aux_mbb_α
    split_ifs <;> norm_num
  · have h2 : (2 : ℕ) ∈ Finset.Icc 1 2 := by simp
    calc (1 : ℝ) = aux_mbb_α 2 := by simp [aux_mbb_α]
      _ ≤ _ := Finset.le_sup' aux_mbb_α h2

end HighDimStat.TailBounds

open HighDimStat.TailBounds

theorem solution : ¬ (∀ {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)),
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))) := by
  intro H
  have hn : (1 : ℕ) ≤ 2 := by norm_num
  have key := @H (ULift Bool) _ _ aux_mbb_mu _ aux_mbb_D (fun _ => 0) aux_mbb_α aux_mbb_filt 2 hn
    (by
      intro k hk
      rw [aux_mbb_filt_pos (by simp at hk; omega)]
      exact Measurable.of_discrete)
    (fun k _ => Integrable.of_finite)
    (by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
      · rw [show (1 - 1 : ℕ) = 0 from rfl, aux_mbb_filt_zero, condExp_bot, aux_mbb_int_D1]
        rfl
      · have : aux_mbb_D 2 = 0 := by
          funext ω; simp [aux_mbb_D]
        rw [this, condExp_zero])
    (fun k _ lam _ => Integrable.of_finite)
    (by
      intro k hk lam hlam
      simp only [Finset.mem_Icc] at hk
      rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
      · exfalso
        simp only [aux_mbb_α, if_true] at hlam
        rcases hlam with h | h
        · norm_num at h
        · have := abs_nonneg lam
          norm_num at h
          linarith
      · have : (fun ω => Real.exp (lam * aux_mbb_D 2 ω)) = fun _ => (1 : ℝ) := by
          funext ω; simp [aux_mbb_D]
        rw [this, condExp_const (aux_mbb_filt.le _)]
        exact Filter.Eventually.of_forall (fun _ => by simp))
  have h2 := key.2 2 (by norm_num)
  rw [aux_mbb_sup] at h2
  have hset : {ω | (2 : ℝ) ≤ |∑ k ∈ Finset.Icc 1 2, aux_mbb_D k ω|} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, aux_mbb_sum]
    cases ω with | up b => cases b <;> simp [aux_mbb_D]
  rw [hset, probReal_univ] at h2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    zero_div] at h2
  rw [if_neg (by norm_num)] at h2
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hexp : Real.exp (-2 / (2 * 1)) = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  rw [hexp] at h2
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have : 2 * (Real.exp 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]; exact he
  linarith
