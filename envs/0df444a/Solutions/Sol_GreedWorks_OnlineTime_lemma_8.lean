-- Prove2me | solution 1 for GreedWorks.OnlineTime.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:14.43772+00:00
-- url     : https://prove2.me/submissions/68376d05-7752-4a25-81d0-3c340751be5e

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_Greedy
import Definitions.Def_GreedWorks_OnlineTime_StochasticGreedy

open GreedWorks.OnlineTime MeasureTheory ProbabilityTheory Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace Lemma8Helper

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

private lemma max_sub_le_quad_small (x μ c : ℝ) (hc : 0 < c) :
    max 0 (x - μ) ≤ ((x - μ) ^ 2 + 2 * c * (x - μ) + c ^ 2) / (4 * c) := by
  have hc4 : 0 < 4 * c := by positivity
  refine max_le ?_ ?_
  · have hsq : 0 ≤ (x - μ + c) ^ 2 := sq_nonneg (x - μ + c)
    have h_eq : (x - μ + c) ^ 2 = (x - μ) ^ 2 + 2 * c * (x - μ) + c ^ 2 := by ring
    rw [← h_eq]
    exact div_nonneg hsq (le_of_lt hc4)
  · rw [le_div_iff₀ hc4]
    have hsq : 0 ≤ (x - μ - c) ^ 2 := sq_nonneg (x - μ - c)
    linarith

private lemma max_sub_le_quad_large (x μ Δ : ℝ) (hx : 0 ≤ x) (hμ : 0 < μ) (hΔ : 1 ≤ Δ) :
    max 0 (x - μ) ≤
      ((x - μ) ^ 2 + μ * (Δ ^ 2 + 1) * (x - μ) + Δ ^ 2 * μ ^ 2) / (μ * (Δ + 1) ^ 2) := by
  have hden : 0 < μ * (Δ + 1) ^ 2 := by positivity
  have h_id : (x - μ) ^ 2 + μ * (Δ ^ 2 + 1) * (x - μ) + Δ ^ 2 * μ ^ 2 =
      x ^ 2 + μ * (Δ ^ 2 - 1) * x := by ring
  refine max_le ?_ ?_
  · rw [h_id]
    have hΔ2 : 0 ≤ Δ ^ 2 - 1 := by nlinarith
    have hnum : 0 ≤ x ^ 2 + μ * (Δ ^ 2 - 1) * x := by positivity
    exact div_nonneg hnum (le_of_lt hden)
  · rw [le_div_iff₀ hden, h_id]
    have hsq : 0 ≤ (x - μ * (Δ + 1)) ^ 2 := sq_nonneg (x - μ * (Δ + 1))
    have h_diff : x ^ 2 + μ * (Δ ^ 2 - 1) * x - (x - μ) * (μ * (Δ + 1) ^ 2) =
        (x - μ * (Δ + 1)) ^ 2 := by ring
    linarith

private lemma integral_sub_mean_eq_zero (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX : Integrable X Pr) :
    ∫ ω, (X ω - ∫ ω', X ω' ∂Pr) ∂Pr = 0 := by
  rw [integral_sub hX (integrable_const _), integral_const]
  have huniv : Pr.real Set.univ = 1 := by simp [Measure.real]
  rw [smul_eq_mul, huniv, one_mul, sub_self]

private lemma integrable_sub_mean_sq (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX2 : MemLp X 2 Pr) :
    Integrable (fun ω => (X ω - ∫ ω', X ω' ∂Pr) ^ 2) Pr := by
  have hsub : MemLp (fun ω => X ω - ∫ ω', X ω' ∂Pr) 2 Pr :=
    hX2.sub (memLp_const _)
  exact hsub.integrable_sq

private lemma integrable_max_sub_mean (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX : Integrable X Pr) :
    Integrable (fun ω => max 0 (X ω - ∫ ω', X ω' ∂Pr)) Pr :=
  (integrable_const 0).sup (hX.sub (integrable_const _))

private lemma integrable_quad_sub_mean (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX2 : MemLp X 2 Pr) (b d : ℝ) :
    Integrable (fun ω => (X ω - ∫ ω', X ω' ∂Pr) ^ 2 + b * (X ω - ∫ ω', X ω' ∂Pr) + d) Pr := by
  let μ := ∫ ω', X ω' ∂Pr
  have hX : Integrable X Pr := hX2.integrable one_le_two
  have h1 : Integrable (fun ω => (X ω - μ) ^ 2) Pr := integrable_sub_mean_sq Pr X hX2
  have h2 : Integrable (fun ω => b * (X ω - μ)) Pr := (hX.sub (integrable_const μ)).const_mul b
  exact (h1.add h2).add (integrable_const d)

private lemma integral_quad_sub_mean (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX2 : MemLp X 2 Pr) (b d : ℝ) :
    ∫ ω, ((X ω - ∫ ω', X ω' ∂Pr) ^ 2 + b * (X ω - ∫ ω', X ω' ∂Pr) + d) ∂Pr =
      (∫ ω, (X ω - ∫ ω', X ω' ∂Pr) ^ 2 ∂Pr) + d := by
  let μ := ∫ ω', X ω' ∂Pr
  have hX : Integrable X Pr := hX2.integrable one_le_two
  have h1 : Integrable (fun ω => (X ω - μ) ^ 2) Pr := integrable_sub_mean_sq Pr X hX2
  have h2 : Integrable (fun ω => b * (X ω - μ)) Pr := (hX.sub (integrable_const μ)).const_mul b
  have h12 : Integrable (fun ω => (X ω - μ) ^ 2 + b * (X ω - μ)) Pr := h1.add h2
  have h3 : Integrable (fun _ : Ω => d) Pr := integrable_const d
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul,
    integral_sub_mean_eq_zero Pr X hX, integral_const]
  have huniv : Pr.real Set.univ = 1 := by simp [Measure.real]
  rw [smul_eq_mul, huniv, one_mul, mul_zero, add_zero]

private lemma integral_max_sub_le_of_pos (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX2 : MemLp X 2 Pr) (Δ : ℝ)
    (hvar : variance X Pr ≤ Δ * (∫ ω, X ω ∂Pr) ^ 2)
    (c : ℝ) (hc : 0 < c) :
    ∫ ω, max 0 (X ω - ∫ ω', X ω' ∂Pr) ∂Pr ≤
      (Δ * (∫ ω, X ω ∂Pr) ^ 2 + c ^ 2) / (4 * c) := by
  let μ := ∫ ω, X ω ∂Pr
  have hX : Integrable X Pr := hX2.integrable one_le_two
  have h_rhs_int : Integrable (fun ω => ((X ω - μ) ^ 2 + (2 * c) * (X ω - μ) + c ^ 2) / (4 * c)) Pr :=
    (integrable_quad_sub_mean Pr X hX2 (2 * c) (c ^ 2)).div_const (4 * c)
  have h_mono : ∫ ω, max 0 (X ω - μ) ∂Pr ≤
      ∫ ω, ((X ω - μ) ^ 2 + (2 * c) * (X ω - μ) + c ^ 2) / (4 * c) ∂Pr := by
    refine integral_mono_ae (integrable_max_sub_mean Pr X hX) h_rhs_int
      (Filter.Eventually.of_forall (fun ω => max_sub_le_quad_small (X ω) μ c hc))
  have h_eval : ∫ ω, ((X ω - μ) ^ 2 + (2 * c) * (X ω - μ) + c ^ 2) / (4 * c) ∂Pr =
      ((∫ ω, (X ω - μ) ^ 2 ∂Pr) + c ^ 2) / (4 * c) := by
    rw [integral_div, integral_quad_sub_mean Pr X hX2 (2 * c) (c ^ 2)]
  have h_var_eq : ∫ ω, (X ω - μ) ^ 2 ∂Pr = variance X Pr :=
    (variance_eq_integral hX2.aemeasurable).symm
  have hc4 : 0 ≤ 4 * c := by positivity
  calc ∫ ω, max 0 (X ω - μ) ∂Pr
      ≤ ((∫ ω, (X ω - μ) ^ 2 ∂Pr) + c ^ 2) / (4 * c) := by linarith
    _ ≤ (Δ * μ ^ 2 + c ^ 2) / (4 * c) := by
      rw [h_var_eq]
      exact div_le_div_of_nonneg_right (by linarith) hc4

private lemma extremal_bound (I : StochasticInstance M n Ω) (i : M) (k : Fin n)
    (helig : I.eligible i k) :
    haveI := I.probability
    ∫ ω, max 0 ((I.P i k ω : ℝ) - mean I i k) ∂I.Pr ≤
      (hFactor I.Delta - 1) * mean I i k := by
  letI := I.probability
  let X : Ω → ℝ := fun ω => (I.P i k ω : ℝ)
  let μ : ℝ := mean I i k
  have hX2 : MemLp X 2 I.Pr := I.memLp i k helig
  have hX : Integrable X I.Pr := hX2.integrable one_le_two
  have hμ_ge_one : 1 ≤ μ := I.meanAtLeastOne i k helig
  have hμ_pos : 0 < μ := by linarith
  have hvar : variance X I.Pr ≤ I.Delta * μ ^ 2 := I.cvBound i k helig
  have hΔ_nonneg : 0 ≤ I.Delta := I.Delta_nonneg
  unfold hFactor
  split_ifs with hΔ1
  · rw [add_sub_cancel_left]
    rcases eq_or_lt_of_le hΔ_nonneg with hΔ0 | hΔ_pos
    · rw [← hΔ0, Real.sqrt_zero, zero_div, zero_mul]
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      rw [zero_add]
      have hstep := integral_max_sub_le_of_pos I.Pr X hX2 I.Delta hvar (4 * ε) (by positivity)
      rw [← hΔ0] at hstep
      have h_simp : (0 * (∫ ω, X ω ∂I.Pr) ^ 2 + (4 * ε) ^ 2) / (4 * (4 * ε)) = ε := by
        field_simp [ne_of_gt hε]
        ring
      rw [h_simp] at hstep
      exact hstep
    · let c := μ * Real.sqrt I.Delta
      have hc_pos : 0 < c := mul_pos hμ_pos (Real.sqrt_pos.mpr hΔ_pos)
      have hstep := integral_max_sub_le_of_pos I.Pr X hX2 I.Delta hvar c hc_pos
      have hc_sq : c ^ 2 = I.Delta * μ ^ 2 := by
        dsimp [c]
        rw [mul_pow, Real.sq_sqrt hΔ_nonneg, mul_comm]
      have h_alg : (I.Delta * μ ^ 2 + c ^ 2) / (4 * c) = Real.sqrt I.Delta / 2 * μ := by
        rw [hc_sq]
        have : I.Delta * μ ^ 2 + I.Delta * μ ^ 2 = 2 * c * c := by
          rw [← hc_sq]; ring
        rw [this]
        dsimp [c]
        field_simp [ne_of_gt hμ_pos, ne_of_gt (Real.sqrt_pos.mpr hΔ_pos)]
        ring
      exact le_trans hstep (le_of_eq h_alg)
  · rw [add_sub_cancel_left]
    have hΔ_ge_one : 1 ≤ I.Delta := le_of_not_ge hΔ1
    let a1 := μ * (I.Delta ^ 2 + 1)
    let a0 := I.Delta ^ 2 * μ ^ 2
    let den := μ * (I.Delta + 1) ^ 2
    have hden_pos : 0 < den := by positivity
    have h_rhs_int : Integrable (fun ω => ((X ω - μ) ^ 2 + a1 * (X ω - μ) + a0) / den) I.Pr :=
      (integrable_quad_sub_mean I.Pr X hX2 a1 a0).div_const den
    have h_mono : ∫ ω, max 0 (X ω - μ) ∂I.Pr ≤
        ∫ ω, ((X ω - μ) ^ 2 + a1 * (X ω - μ) + a0) / den ∂I.Pr := by
      refine integral_mono_ae (integrable_max_sub_mean I.Pr X hX) h_rhs_int
        (Filter.Eventually.of_forall (fun ω =>
          max_sub_le_quad_large (X ω) μ I.Delta (Nat.cast_nonneg _) hμ_pos hΔ_ge_one))
    have h_eval : ∫ ω, ((X ω - μ) ^ 2 + a1 * (X ω - μ) + a0) / den ∂I.Pr =
        ((∫ ω, (X ω - μ) ^ 2 ∂I.Pr) + a0) / den := by
      rw [integral_div]
      exact congrArg (· / den) (integral_quad_sub_mean I.Pr X hX2 a1 a0)
    have h_var_eq : ∫ ω, (X ω - μ) ^ 2 ∂I.Pr = variance X I.Pr :=
      (variance_eq_integral hX2.aemeasurable).symm
    have h_step2 : ((∫ ω, (X ω - μ) ^ 2 ∂I.Pr) + a0) / den ≤
        (I.Delta * μ ^ 2 + a0) / den := by
      rw [h_var_eq]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hden_pos)
    have h_alg : (I.Delta * μ ^ 2 + a0) / den = I.Delta / (I.Delta + 1) * μ := by
      dsimp [a0, den]
      have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
      have hΔ1_ne : I.Delta + 1 ≠ 0 := by linarith
      field_simp [hμ_ne, hΔ1_ne]
      ring
    linarith

private lemma nominalPred_spec (elig : M → Fin n → Prop) (r : Fin n → ℕ)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j) (w : Fin n → ℝ)
    (c : ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) {j k : Fin n}
    (hpred : nominalPred m s j = some k) :
    m k = m j ∧ s k + p (m k) k ≤ s j := by
  unfold nominalPred at hpred
  dsimp only [] at hpred
  split_ifs at hpred with hB
  have hk_eq : Classical.choose
      ((Finset.univ.filter (fun k' => m k' = m j ∧ s k' < s j)).exists_max_image s hB) = k :=
    Option.some.inj hpred
  have hk_spec := Classical.choose_spec
    ((Finset.univ.filter (fun k' => m k' = m j ∧ s k' < s j)).exists_max_image s hB)
  rw [hk_eq] at hk_spec
  have hmk : m k = m j := (Finset.mem_filter.mp hk_spec.1).2.1
  have hsk_lt : s k < s j := (Finset.mem_filter.mp hk_spec.1).2.2
  refine ⟨hmk, ?_⟩
  by_contra! hgt
  have hne : k ≠ j := by intro heq; subst heq; linarith
  have hdisj := hG.2.2.1 k j hne hmk
  have hpj_pos : 0 < p (m j) j := by
    have := hp (m j) j (hG.1 j).1; linarith
  have hmem1 : s j ∈ Set.Ico (s k) (s k + p (m k) k) := ⟨le_of_lt hsk_lt, hgt⟩
  have hmem2 : s j ∈ Set.Ico (s j) (s j + p (m j) j) := ⟨le_refl _, by linarith⟩
  exact Set.disjoint_left.mp hdisj hmem1 hmem2

private def excessSum (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (ω : Ω) : ℕ → Fin n → ℝ
  | 0, _ => 0
  | fuel + 1, j =>
    match nominalPred m s j with
    | none => 0
    | some k => excessSum I m s ω fuel k + max 0 ((I.P (m k) k ω : ℝ) - mean I (m k) k)

private def meanSum (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0, _ => 0
  | fuel + 1, j =>
    match nominalPred m s j with
    | none => 0
    | some k => meanSum I m s fuel k + mean I (m k) k

private lemma excessSum_nonneg (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (ω : Ω) (fuel : ℕ) : ∀ j : Fin n, 0 ≤ excessSum I m s ω fuel j := by
  induction fuel with
  | zero => intro _; exact le_refl 0
  | succ fuel ih =>
    intro j
    unfold excessSum
    cases nominalPred m s j with
    | none => exact le_refl 0
    | some k => exact add_nonneg (ih k) (le_max_left 0 _)

private lemma stochStartAux_le_add_excessSum (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (ω : Ω) (fuel : ℕ) :
    ∀ j : Fin n, stochStartAux m s (realize I ω) fuel j ≤ s j + excessSum I m s ω fuel j := by
  induction fuel with
  | zero =>
    intro j
    simp [stochStartAux, excessSum]
  | succ fuel ih =>
    intro j
    unfold stochStartAux excessSum
    cases hpred : nominalPred m s j with
    | none => simp
    | some k =>
      simp only []
      have hspec := nominalPred_spec I.eligible I.release (mean I) I.meanAtLeastOne
        I.weight (2 / 3) m s hG hpred
      have hstep := ih k
      have hex_nonneg := excessSum_nonneg I m s ω fuel k
      have hmax0 : 0 ≤ max 0 ((I.P (m k) k ω : ℝ) - mean I (m k) k) := le_max_left 0 _
      have hmax_sub : (I.P (m k) k ω : ℝ) - mean I (m k) k ≤
          max 0 ((I.P (m k) k ω : ℝ) - mean I (m k) k) := le_max_right 0 _
      have hreal : (realize I ω (m k) k : ℝ) = (I.P (m k) k ω : ℝ) := rfl
      rw [hreal]
      refine max_le (by linarith) (by linarith [hspec.2])

private lemma meanSum_le_start (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (fuel : ℕ) :
    ∀ j : Fin n, meanSum I m s fuel j ≤ s j := by
  have hs_nonneg : ∀ j : Fin n, 0 ≤ s j := by
    intro j
    have hmod := hG.2.1 j
    have hr : 0 ≤ modRelease (2 / 3) I.release (mean I) (m j) j :=
      le_trans (Nat.cast_nonneg (I.release j)) (le_max_left _ _)
    linarith
  induction fuel with
  | zero =>
    intro j
    exact hs_nonneg j
  | succ fuel ih =>
    intro j
    unfold meanSum
    cases hpred : nominalPred m s j with
    | none => exact hs_nonneg j
    | some k =>
      simp only []
      have hspec := nominalPred_spec I.eligible I.release (mean I) I.meanAtLeastOne
        I.weight (2 / 3) m s hG hpred
      have hstep := ih k
      linarith [hspec.2]

private lemma integrable_stochStartAux (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (fuel : ℕ) :
    haveI := I.probability
    ∀ j : Fin n, Integrable (fun ω => stochStartAux m s (realize I ω) fuel j) I.Pr := by
  letI := I.probability
  induction fuel with
  | zero =>
    intro j
    exact integrable_const (s j)
  | succ fuel ih =>
    intro j
    unfold stochStartAux
    cases nominalPred m s j with
    | none => exact integrable_const (s j)
    | some k =>
      have hPk : Integrable (fun ω => (I.P (m k) k ω : ℝ)) I.Pr :=
        (I.memLp (m k) k (hG.1 k).1).integrable one_le_two
      exact (integrable_const (s j)).sup ((ih k).add hPk)

private lemma integrable_excessSum (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (fuel : ℕ) :
    haveI := I.probability
    ∀ j : Fin n, Integrable (fun ω => excessSum I m s ω fuel j) I.Pr := by
  letI := I.probability
  induction fuel with
  | zero =>
    intro _
    exact integrable_const 0
  | succ fuel ih =>
    intro j
    unfold excessSum
    cases nominalPred m s j with
    | none => exact integrable_const 0
    | some k =>
      have hPk : Integrable (fun ω => (I.P (m k) k ω : ℝ)) I.Pr :=
        (I.memLp (m k) k (hG.1 k).1).integrable one_le_two
      exact (ih k).add (integrable_max_sub_mean I.Pr (fun ω => (I.P (m k) k ω : ℝ)) hPk)

private lemma integral_excessSum_le (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (fuel : ℕ) :
    haveI := I.probability
    ∀ j : Fin n, ∫ ω, excessSum I m s ω fuel j ∂I.Pr ≤
      (hFactor I.Delta - 1) * meanSum I m s fuel j := by
  letI := I.probability
  induction fuel with
  | zero =>
    intro j
    simp [excessSum, meanSum]
  | succ fuel ih =>
    intro j
    unfold excessSum meanSum
    cases nominalPred m s j with
    | none => simp
    | some k =>
      simp only []
      have hPk : Integrable (fun ω => (I.P (m k) k ω : ℝ)) I.Pr :=
        (I.memLp (m k) k (hG.1 k).1).integrable one_le_two
      have hmax_int : Integrable (fun ω => max 0 ((I.P (m k) k ω : ℝ) - mean I (m k) k)) I.Pr :=
        integrable_max_sub_mean I.Pr (fun ω => (I.P (m k) k ω : ℝ)) hPk
      rw [integral_add (integrable_excessSum I m s hG fuel k) hmax_int]
      have h1 := ih k
      have h2 := extremal_bound I (m k) k (hG.1 k).1
      linarith

private lemma hFactor_sub_one_nonneg (Δ : ℝ) (hΔ : 0 ≤ Δ) : 0 ≤ hFactor Δ - 1 := by
  unfold hFactor
  split_ifs
  · rw [add_sub_cancel_left]
    positivity
  · rw [add_sub_cancel_left]
    positivity

end Lemma8Helper

open Lemma8Helper

theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s) (j : Fin n) :
    ∫ ω, stochStart m s (realize I ω) j ∂I.Pr ≤ hFactor I.Delta * s j := by
  letI := I.probability
  unfold stochStart
  have h_pw : ∀ ω, stochStartAux m s (realize I ω) n j ≤ s j + excessSum I m s ω n j :=
    fun ω => stochStartAux_le_add_excessSum I m s hG ω n j
  have h_int_lhs := integrable_stochStartAux I m s hG n j
  have h_int_ex := integrable_excessSum I m s hG n j
  have h_int_rhs := (integrable_const (s j)).add h_int_ex
  have h_mono : ∫ ω, stochStartAux m s (realize I ω) n j ∂I.Pr ≤
      ∫ ω, (s j + excessSum I m s ω n j) ∂I.Pr :=
    integral_mono_ae h_int_lhs h_int_rhs (Filter.Eventually.of_forall h_pw)
  rw [integral_add (integrable_const (s j)) h_int_ex, integral_const] at h_mono
  have huniv : I.Pr.real Set.univ = 1 := by simp [Measure.real]
  rw [smul_eq_mul, huniv, one_mul] at h_mono
  have h_ex_le := integral_excessSum_le I m s hG n j
  have h_mean_le := meanSum_le_start I m s hG n j
  have h_hpos := hFactor_sub_one_nonneg I.Delta I.Delta_nonneg
  have h_prod_le : (hFactor I.Delta - 1) * meanSum I m s n j ≤ (hFactor I.Delta - 1) * s j :=
    mul_le_mul_of_nonneg_left h_mean_le h_hpos
  linarith
