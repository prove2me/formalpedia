-- Prove2me | solution 1 for NetworkControl.UtilityFairness.lemma_lyapunov_drift_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:06:00.673505+00:00
-- url     : https://prove2.me/submissions/55749a79-17dd-4d68-aaa4-d372b38a003e

import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift



namespace NetworkControl.UtilityFairness

open MeasureTheory

lemma h24_comap_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} (U : Ω → Fin N → ℝ)
    (h : ∀ i : Fin N, Measurable (fun ω => U ω i)) :
    MeasurableSpace.comap U inferInstance ≤ mΩ :=
  (measurable_pi_iff.mpr h).comap_le

lemma h24_integral_drift {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : ℕ} (L : (Fin N → ℝ) → ℝ) (U : ℕ → Ω → Fin N → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P) (t : ℕ) :
    ∫ ω, drift P L U t ω ∂P = ∫ ω, L (U (t+1) ω) ∂P - ∫ ω, L (U t ω) ∂P := by
  unfold drift
  rw [integral_condExp (h24_comap_le (U t) (hMeasU t))]
  exact integral_sub (hIntegL (t+1)) (hIntegL t)

lemma h24_integrable_drift {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (U : ℕ → Ω → Fin N → ℝ) (t : ℕ) :
    Integrable (drift P L U t) P := by
  unfold drift
  exact integrable_condExp

lemma h24_limsup_liminf (a b : ℕ → ℝ) (C : ℝ) (h : ∀ t : ℕ, 1 ≤ t → a t ≤ b t + C / t) :
    (Filter.limsup (fun t => ((a t : ℝ) : EReal)) Filter.atTop
      ≤ Filter.limsup (fun t => ((b t : ℝ) : EReal)) Filter.atTop) ∧
    (Filter.liminf (fun t => ((a t : ℝ) : EReal)) Filter.atTop
      ≤ Filter.liminf (fun t => ((b t : ℝ) : EReal)) Filter.atTop) := by
  have hC : Filter.Tendsto (fun t : ℕ => C / (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  constructor
  · by_contra hlt
    push_neg at hlt
    obtain ⟨d, hd1, hd2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨d', h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hd1
    have hd'd : d' < d := by exact_mod_cast h2
    have e1 := Filter.eventually_lt_of_limsup_lt h1
    have e2 : ∀ᶠ t : ℕ in Filter.atTop, C / (t : ℝ) < d - d' :=
      hC.eventually (gt_mem_nhds (by linarith))
    have e3 : ∀ᶠ t : ℕ in Filter.atTop, 1 ≤ t := Filter.eventually_ge_atTop 1
    have e4 : ∀ᶠ t : ℕ in Filter.atTop, ((a t : ℝ) : EReal) ≤ (d : EReal) := by
      filter_upwards [e1, e2, e3] with t h1 h2 h3
      have h1' : b t < d' := by exact_mod_cast h1
      have := h t h3
      exact_mod_cast (by linarith : a t ≤ d)
    have := Filter.limsup_le_of_le (by isBoundedDefault) e4
    exact absurd (lt_of_le_of_lt this hd2) (lt_irrefl _)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨d, hd1, hd2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨d', h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hd1
    have hd'd : d' < d := by exact_mod_cast h2
    have e1 := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) h1
    have e2 : ∀ᶠ t : ℕ in Filter.atTop, C / (t : ℝ) < d - d' :=
      hC.eventually (gt_mem_nhds (by linarith))
    have e3 : ∀ᶠ t : ℕ in Filter.atTop, 1 ≤ t := Filter.eventually_ge_atTop 1
    have e5 := Filter.eventually_lt_of_lt_liminf hd2 (by isBoundedDefault)
    have e6 := e1.and_eventually (e2.and (e3.and e5))
    obtain ⟨t, ht1, ht2, ht3, ht4⟩ := e6.exists
    have h1' : b t < d' := by exact_mod_cast ht1
    have h4' : d < a t := by exact_mod_cast ht4
    have := h t ht3
    linarith

lemma h24_jensen_vec {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : ℕ} (g : (Fin K → ℝ) → ℝ) (hg : ConcaveOn ℝ Set.univ g)
    (R : Ω → Fin K → ℝ) (hR : ∀ k, Integrable (fun ω => R ω k) P)
    (hgR : Integrable (fun ω => g (R ω)) P) :
    ∫ ω, g (R ω) ∂P ≤ g (fun k => ∫ ω, R ω k ∂P) := by
  have hc : ContinuousOn g Set.univ := hg.continuousOn isOpen_univ
  have := hg.le_map_integral hc isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (integrable_pi_iff.2 hR) hgR
  have heq : (∫ ω, R ω ∂P) = fun k => ∫ ω, R ω k ∂P := by
    funext k; exact eval_integral hR k
  rwa [heq] at this

lemma h24_jensen_avg {K : ℕ} (g : (Fin K → ℝ) → ℝ) (hg : ConcaveOn ℝ Set.univ g)
    (v : ℕ → Fin K → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, g (v τ)
      ≤ g (fun k => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, v τ k) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have := hg.le_map_sum (t := Finset.range t) (w := fun _ => 1 / (t : ℝ)) (p := v)
    (fun _ _ => by positivity)
    (by simp; field_simp) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at this
  rw [← Finset.mul_sum] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  funext k
  simp [Finset.sum_apply, Finset.mul_sum]

lemma h24_lemma_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (x y : ℕ → Ω → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegX : ∀ t : ℕ, Integrable (x t) P)
    (hIntegY : ∀ t : ℕ, Integrable (y t) P)
    (hdrift : ∀ t : ℕ,
      drift P L U t
        ≤ᵐ[P] ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance]))) :
    (Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) ∧
    (Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) := by
  have hm : ∀ t, MeasurableSpace.comap (U t) inferInstance ≤ mΩ :=
    fun t => h24_comap_le (U t) (hMeasU t)
  have step : ∀ t : ℕ, ∫ ω, L (U (t+1) ω) ∂P - ∫ ω, L (U t ω) ∂P
      ≤ ∫ ω, y t ω ∂P - ∫ ω, x t ω ∂P := by
    intro t
    rw [← h24_integral_drift L U hMeasU hIntegL t]
    calc ∫ ω, drift P L U t ω ∂P
        ≤ ∫ ω, ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance])) ω ∂P :=
          integral_mono_ae (h24_integrable_drift L U t)
            (integrable_condExp.sub integrable_condExp) (hdrift t)
      _ = ∫ ω, y t ω ∂P - ∫ ω, x t ω ∂P := by
          have e1 : ∫ ω, (P[y t | MeasurableSpace.comap (U t) inferInstance]) ω ∂P
              = ∫ ω, y t ω ∂P := integral_condExp (hm t)
          have e2 : ∫ ω, (P[x t | MeasurableSpace.comap (U t) inferInstance]) ω ∂P
              = ∫ ω, x t ω ∂P := integral_condExp (hm t)
          simp only [Pi.sub_apply]
          rw [integral_sub integrable_condExp integrable_condExp, e1, e2]
  set C : ℝ := ∫ ω, L (U 0 ω) ∂P with hCdef
  have hsum : ∀ t : ℕ, ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P
      ≤ ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P + C := by
    intro t
    have h1 := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.range t) => step τ)
    rw [Finset.sum_range_sub (fun τ => ∫ ω, L (U τ ω) ∂P), Finset.sum_sub_distrib] at h1
    have h2 : 0 ≤ ∫ ω, L (U t ω) ∂P := integral_nonneg (fun ω => hLnn _)
    linarith
  apply h24_limsup_liminf _ _ C
  intro t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have := hsum t
  have h3 : (1 / (t:ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P
      ≤ (1 / (t:ℝ)) * (∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P + C) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  calc _ ≤ _ := h3
    _ = _ := by ring

end NetworkControl.UtilityFairness

open NetworkControl.UtilityFairness
open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (x y : ℕ → Ω → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegX : ∀ t : ℕ, Integrable (x t) P)
    (hIntegY : ∀ t : ℕ, Integrable (y t) P)
    (hdrift : ∀ t : ℕ,
      drift P L U t
        ≤ᵐ[P] ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance]))) :
    (Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) ∧
    (Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) := by
  exact h24_lemma_core L hLnn U x y hMeasU hIntegL hIntegX hIntegY hdrift
