-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.bound_on_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:09:46.286947+00:00
-- url     : https://prove2.me/submissions/9af2ccef-576f-4618-a59c-4a8a9c79708f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_4
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_5
import Theorems.Thm_LostSalesExpGap_ConstOrder_chernoff_step
import Theorems.Thm_LostSalesExpGap_ConstOrder_vartheta_pos_gamma_lt_one

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open LostSalesExpGap.ConstOrder in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ∀ m : ℕ, 1 ≤ m →
      c.h * (EIL P (rInf P c) m - EIL P (rL P c m) m) - c.p * (rInf P c - rL P c m) ≤
        c.h * (CappedBaseStock.mean P - rInf P c) * (1 - gamma P c)⁻¹ * gamma P c ^ (m + 1) := by
  intro m hm
  obtain ⟨hK, _, _⟩ := lemma_3 P c hP
  have h4 := lemma_4 P c hP m hm
  have h5 := lemma_5 P c hP
  have hch := chernoff_step P c
  obtain ⟨hγ0, hγ1, _⟩ := vartheta_pos_gamma_lt_one P c hP
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set μ := CappedBaseStock.demandPathLaw P with hμ
  set γ := gamma P c
  set mean := CappedBaseStock.mean P
  set r := rInf P c
  set s := rL P c m
  have hmean : 0 < mean := P.positiveMean
  -- r and s lie in [0, mean]
  have hIcc : ∀ A : Set ℝ, A ⊆ Set.Icc 0 mean → 0 ≤ sInf A ∧ sInf A ≤ mean := by
    intro A hA
    by_cases hne : A.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hb : BddBelow A := ⟨0, fun y hy => (hA hy).1⟩
      exact ⟨le_csInf ⟨x, hx⟩ fun y hy => (hA hy).1, le_trans (csInf_le hb hx) (hA hx).2⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]; exact ⟨le_rfl, hmean.le⟩
  obtain ⟨hr0, hrm⟩ := hIcc (argminConst P c) (fun x hx => hx.1)
  obtain ⟨hs0, hsm⟩ := hIcc (argminCL P c m) (fun x hx => hx.1)
  change 0 ≤ r at hr0; change r ≤ mean at hrm
  change 0 ≤ s at hs0; change s ≤ mean at hsm
  -- probabilities p_n
  let A : ℕ → Set CappedBaseStock.DemandPath := fun n =>
    {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * r}
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le (by fun_prop) (by fun_prop)
  let pn : ℕ → ℝ := fun n => μ.real (A n)
  have hpn0 : ∀ n, 0 ≤ pn n := fun n => measureReal_nonneg
  have hpnγ : ∀ n, pn n ≤ γ ^ (n + 1) := by
    intro n
    have := hch (n + 1) (by omega)
    have h' : μ (A n) ≤ ENNReal.ofReal (γ ^ (n + 1)) := by
      simpa [A, Nat.cast_add, Nat.cast_one] using this
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h'
    rwa [ENNReal.toReal_ofReal (pow_nonneg hγ0 _)] at this
  have hgeo : Summable (fun n : ℕ => γ ^ (n + 1)) := by
    simp_rw [pow_succ]
    exact (summable_geometric_of_lt_one hγ0 hγ1).mul_right γ
  have hsum : Summable pn := Summable.of_nonneg_of_le hpn0 hpnγ hgeo
  -- Lemma 5 in real form
  have h5' : c.p / c.h ≤ ∑' n, pn n := by
    have : (∑' n : ℕ, μ (A n)) = ENNReal.ofReal (∑' n, pn n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hpn0 hsum]
      congr 1; funext n
      exact (ofReal_measureReal (measure_ne_top _ _)).symm
    have h5'' : ENNReal.ofReal (c.p / c.h) ≤ ENNReal.ofReal (∑' n, pn n) := by
      rw [← this]; exact h5
    exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hpn0)).mp h5''
  -- tail bound
  have htail : ∑' n, pn n ≤ ∑ n ∈ Finset.range m, pn n + γ ^ (m + 1) * (1 - γ)⁻¹ := by
    rw [← hsum.sum_add_tsum_nat_add m]
    gcongr
    calc ∑' n, pn (n + m) ≤ ∑' n : ℕ, γ ^ (m + 1) * γ ^ n := by
          refine Summable.tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff m).mpr hsum)
            ((summable_geometric_of_lt_one hγ0 hγ1).mul_left _)
          refine (hpnγ (n + m)).trans (le_of_eq ?_)
          rw [← pow_add]; congr 1; ring
      _ = γ ^ (m + 1) * (1 - γ)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hγ0 hγ1]
  -- Kingman series comparison
  let f : ℝ → ℕ → CappedBaseStock.DemandPath → ℝ := fun x n d =>
    max (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
  have hfint : ∀ x, 0 ≤ x → ∀ n, Integrable (f x n) μ := by
    intro x hx n
    refine Integrable.of_bound (C := ((n : ℝ) + 1) * x) ?_ (ae_of_all _ fun d => ?_)
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
    · have hS : 0 ≤ ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) (by positivity)
  have hpt : ∀ n d, f r n d + ((n : ℝ) + 1) * (s - r) * (A n).indicator (fun _ => (1 : ℝ)) d
      ≤ f s n d := by
    intro n d
    simp only [f, A, Set.indicator, Set.mem_setOf_eq]
    have hsr : 0 ≤ s - r := by linarith
    split_ifs with hd
    · rw [max_eq_left (by linarith)]
      have : ((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) + ((n : ℝ) + 1) * (s - r) * 1
          = ((n : ℝ) + 1) * s - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by ring
      rw [this]; exact le_max_left _ _
    · simp only [mul_zero, add_zero]
      exact max_le_max (by nlinarith) le_rfl
  have hint_n : ∀ n, ∫ d, f r n d ∂μ + ((n : ℝ) + 1) * (s - r) * pn n ≤ ∫ d, f s n d ∂μ := by
    intro n
    have hind : Integrable ((A n).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator (hAm n)
    have := integral_mono ((hfint r hr0 n).add (hind.const_mul (((n : ℝ) + 1) * (s - r))))
      (hfint s hs0 n) (hpt n)
    simp only [Pi.add_apply] at this
    rwa [integral_add (hfint r hr0 n) (hind.const_mul _), integral_const_mul,
      integral_indicator_const _ (hAm n), smul_eq_mul, mul_one] at this
  have hEIL : EIL P r m - EIL P s m ≤ -((s - r) * ∑ n ∈ Finset.range m, pn n) := by
    rw [hK r hr0 hrm m hm, hK s hs0 hsm m hm, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro n _
    have h := hint_n n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    change 1 / ((n : ℝ) + 1) * ∫ d, f r n d ∂μ - 1 / ((n : ℝ) + 1) * ∫ d, f s n d ∂μ
      ≤ -((s - r) * pn n)
    rw [← mul_sub, div_mul_eq_mul_div, one_mul, div_le_iff₀ hn1]
    nlinarith
  -- combine
  have hsr : 0 ≤ s - r := by linarith
  have hG : 0 ≤ γ ^ (m + 1) * (1 - γ)⁻¹ := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hY : c.p - c.h * ∑ n ∈ Finset.range m, pn n ≤ c.h * (γ ^ (m + 1) * (1 - γ)⁻¹) := by
    have h1 : c.p / c.h ≤ ∑ n ∈ Finset.range m, pn n + γ ^ (m + 1) * (1 - γ)⁻¹ := h5'.trans htail
    rw [div_le_iff₀ hh] at h1
    nlinarith
  calc c.h * (EIL P r m - EIL P s m) - c.p * (r - s)
      ≤ (s - r) * (c.p - c.h * ∑ n ∈ Finset.range m, pn n) := by nlinarith [hEIL]
    _ ≤ (s - r) * (c.h * (γ ^ (m + 1) * (1 - γ)⁻¹)) := mul_le_mul_of_nonneg_left hY hsr
    _ ≤ (mean - r) * (c.h * (γ ^ (m + 1) * (1 - γ)⁻¹)) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = c.h * (mean - r) * (1 - γ)⁻¹ * γ ^ (m + 1) := by ring
