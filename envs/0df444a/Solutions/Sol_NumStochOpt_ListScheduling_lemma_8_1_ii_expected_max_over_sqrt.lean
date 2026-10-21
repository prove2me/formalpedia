-- Prove2me | solution 1 for NumStochOpt.ListScheduling.lemma_8_1_ii_expected_max_over_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:35:12.026736+00:00
-- url     : https://prove2.me/submissions/c3b1d759-b636-4396-9fde-c7ed6803f13f

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NumStochOpt.ListScheduling

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P) :
    Tendsto (fun n : ℕ => (∫ ω, maxProcTime n (fun j => p j ω) ∂P) / Real.sqrt n)
      atTop (𝓝 0) := by
  -- the truncated square
  set ind : ℝ → ℝ → ℝ := fun a x => Set.indicator (Set.Ioi a) (fun y : ℝ => y ^ 2) x with hind
  have hind_meas : ∀ a, Measurable (ind a) := fun a =>
    (measurable_id.pow_const 2).indicator measurableSet_Ioi
  have hind_le : ∀ a x, ind a x ≤ x ^ 2 := by
    intro a x
    simp only [hind, Set.indicator]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg x
  have hind_nn : ∀ a x, 0 ≤ ind a x := by
    intro a x
    simp only [hind, Set.indicator]
    split_ifs
    · exact sq_nonneg x
    · exact le_rfl
  have hint2 : ∀ j, Integrable (fun ω => p j ω ^ 2) P := fun j =>
    ((hident j).sq).symm.integrable_snd hsq
  have hint1 : ∀ j, Integrable (p j) P := by
    intro j
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hint2 j))
      (hmeas j).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg j ω)]
    show p j ω ≤ 1 + p j ω ^ 2
    nlinarith [sq_nonneg (p j ω - 1), hnonneg j ω]
  have hindint : ∀ a j, Integrable (fun ω => ind a (p j ω)) P := by
    intro a j
    refine Integrable.mono' (hint2 j) ((hind_meas a).comp (hmeas j)).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hind_nn _ _)]
    exact hind_le _ _
  -- the max
  set M : ℕ → Ω → ℝ := fun n ω => maxProcTime n (fun j => p j ω) with hM
  have hMmeas : ∀ n, Measurable (M n) := by
    intro n
    exact Measurable.iSup (fun i : Fin n => hmeas i)
  have hMnn : ∀ n ω, 0 ≤ M n ω := fun n ω =>
    Real.iSup_nonneg (fun i => hnonneg _ _)
  have hMle_sum : ∀ n ω, M n ω ≤ ∑ j : Fin n, p j ω := by
    intro n ω
    refine Real.iSup_le (fun i => ?_) (Finset.sum_nonneg (fun j _ => hnonneg _ _))
    exact Finset.single_le_sum (f := fun j : Fin n => p j ω) (fun j _ => hnonneg _ _) (Finset.mem_univ i)
  have hMint : ∀ n, Integrable (M n) P := by
    intro n
    have hsi : Integrable (fun ω => ∑ j : Fin n, p j ω) P :=
      integrable_finsetSum _ (fun j _ => hint1 j)
    refine Integrable.mono' hsi (hMmeas n).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnn n ω)]
    exact hMle_sum n ω
  -- truncation bound
  have hbound : ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∀ ω, M n ω ≤ a + (1 / a) * ∑ j : Fin n, ind a (p j ω) := by
    intro n a ha ω
    have hs : 0 ≤ (1 / a) * ∑ j : Fin n, ind a (p j ω) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hind_nn _ _))
    refine Real.iSup_le (fun i => ?_) (by linarith)
    have hi : ind a (p i ω) ≤ ∑ j : Fin n, ind a (p j ω) :=
      Finset.single_le_sum (f := fun j : Fin n => ind a (p j ω)) (fun j _ => hind_nn _ _)
        (Finset.mem_univ i)
    have hpi := hnonneg i ω
    by_cases hc : p i ω ≤ a
    · linarith
    · push_neg at hc
      have h1 : ind a (p i ω) = p i ω ^ 2 := by simp [hind, hc]
      have h2 : p i ω ≤ (1 / a) * ind a (p i ω) := by
        rw [h1, one_div, inv_mul_eq_div, le_div_iff₀ ha]
        nlinarith
      have h3 : (1 / a) * ind a (p i ω) ≤ (1 / a) * ∑ j : Fin n, ind a (p j ω) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      linarith
  -- expectation of the truncation
  have hE : ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∫ ω, M n ω ∂P ≤ a + (1 / a) * (n * ∫ ω, ind a (p 0 ω) ∂P) := by
    intro n a ha
    have hsumint : Integrable (fun ω => ∑ j : Fin n, ind a (p j ω)) P :=
      integrable_finsetSum _ (fun j _ => hindint a j)
    have h1 : ∫ ω, M n ω ∂P ≤ ∫ ω, (a + (1 / a) * ∑ j : Fin n, ind a (p j ω)) ∂P := by
      refine integral_mono (hMint n) ?_ (hbound n a ha)
      exact (integrable_const a).add (hsumint.const_mul _)
    have h2 : ∫ ω, (a + (1 / a) * ∑ j : Fin n, ind a (p j ω)) ∂P =
        a + (1 / a) * (n * ∫ ω, ind a (p 0 ω) ∂P) := by
      rw [integral_add (integrable_const a) (hsumint.const_mul _)]
      rw [integral_const, integral_const_mul]
      have h3 : ∀ j : Fin n, ∫ ω, ind a (p j ω) ∂P = ∫ ω, ind a (p 0 ω) ∂P := fun j =>
        ((hident j).comp (hind_meas a)).integral_eq
      rw [integral_finsetSum (Finset.univ : Finset (Fin n))
        (f := fun (j : Fin n) ω => ind a (p j ω)) (fun j _ => hindint a j)]
      simp [h3]
    linarith
  -- the main estimate
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun δ hδ => ?_⟩
  · refine Eventually.of_forall (fun n => lt_of_lt_of_le ha ?_)
    exact div_nonneg (integral_nonneg (hMnn n)) (Real.sqrt_nonneg _)
  · set ε : ℝ := δ / 2 with hε
    have hεpos : 0 < ε := by positivity
    -- G n → 0
    have hG : Tendsto (fun n : ℕ => ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := P)
        (F := fun (n : ℕ) ω => ind (ε * Real.sqrt n) (p 0 ω)) (f := fun _ => (0 : ℝ))
        (bound := fun ω => p 0 ω ^ 2)
        (fun n => ((hind_meas _).comp (hmeas 0)).aestronglyMeasurable) hsq
        (fun n => ae_of_all _ (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hind_nn _ _)]; exact hind_le _ _))
        (ae_of_all _ (fun ω => ?_))
      · simpa using this
      · have hT : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hεpos
            (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have hev := hT.eventually_gt_atTop (p 0 ω)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp [hind, Set.indicator, not_lt.mpr hn.le]
    have hG' := (tendsto_order.1 hG).2 (ε ^ 2) (by positivity)
    have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    filter_upwards [hG', hn1] with n hGn hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hapos : 0 < ε * Real.sqrt n := by positivity
    have hEn := hE n (ε * Real.sqrt n) hapos
    have hsqsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    rw [div_lt_iff₀ hsq_pos]
    have e1 : (1 / (ε * Real.sqrt n)) * (n * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) =
        Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) := by
      generalize Real.sqrt n = s at hsqsq hsq_pos hapos ⊢
      rw [← hsqsq]; field_simp
    have e2 : (1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P < ε := by
      rw [one_div, inv_mul_lt_iff₀ hεpos]
      nlinarith
    have : ∫ ω, M n ω ∂P < δ * Real.sqrt n := by
      have e3 : ε * Real.sqrt n + Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P)
          < δ * Real.sqrt n := by
        have : Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) < Real.sqrt n * ε :=
          mul_lt_mul_of_pos_left e2 hsq_pos
        nlinarith
      linarith
    exact this
