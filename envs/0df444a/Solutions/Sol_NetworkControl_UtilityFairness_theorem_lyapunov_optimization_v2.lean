-- Prove2me | solution 1 for NetworkControl.UtilityFairness.theorem_lyapunov_optimization_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:08:40.205976+00:00
-- url     : https://prove2.me/submissions/720ac989-a9d1-4d22-ae8a-27ec047058c9

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


lemma h24_part1 (u G : ℕ → ℝ) (ε V B gs C : ℝ) (hε : 0 < ε) (hV : 0 < V)
    (hu0 : ∀ t, 0 ≤ u t)
    (hK : ∀ t : ℕ, 1 ≤ t → ε * u t ≤ (B - V * gs) + V * G t + C / t) :
    (ε : EReal) * Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop
      ≤ (B : EReal) + (V : EReal) *
        (Filter.limsup (fun t => ((G t : ℝ) : EReal)) Filter.atTop - (gs : EReal)) := by
  have hC : Filter.Tendsto (fun t : ℕ => C / (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hM0 : (0 : EReal) ≤ Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop := by
    have : (0 : EReal) ≤ Filter.liminf (fun t => ((u t : ℝ) : EReal)) Filter.atTop :=
      Filter.le_liminf_of_le (by isBoundedDefault)
        (Filter.Eventually.of_forall (fun t => by exact_mod_cast hu0 t))
    exact this.trans Filter.liminf_le_limsup
  have claim : ∀ d q0 : ℝ, ε * q0 = B + V * (d - gs) →
      Filter.limsup (fun t => ((G t : ℝ) : EReal)) Filter.atTop < (d : EReal) →
      Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop ≤ (q0 : EReal) := by
    intro d q0 hq0 hd
    by_contra hq
    push_neg at hq
    obtain ⟨q', hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hq
    have hq1' : q0 < q' := by exact_mod_cast hq1
    have e1 := Filter.eventually_lt_of_limsup_lt hd
    have hδ : 0 < ε * (q' - q0) := mul_pos hε (by linarith)
    have e2 : ∀ᶠ t : ℕ in Filter.atTop, C / (t : ℝ) < ε * (q' - q0) :=
      hC.eventually (gt_mem_nhds hδ)
    have e3 : ∀ᶠ t : ℕ in Filter.atTop, 1 ≤ t := Filter.eventually_ge_atTop 1
    have e4 : ∀ᶠ t : ℕ in Filter.atTop, ((u t : ℝ) : EReal) ≤ (q' : EReal) := by
      filter_upwards [e1, e2, e3] with t h1 h2 h3
      have h1' : G t < d := by exact_mod_cast h1
      have hk := hK t h3
      have : u t ≤ q' := by
        by_contra hc
        push_neg at hc
        have a1 := mul_pos hε (sub_pos.2 hc)
        have a2 := mul_pos hV (sub_pos.2 h1')
        nlinarith
      exact_mod_cast this
    have := Filter.limsup_le_of_le (by isBoundedDefault) e4
    exact absurd (lt_of_le_of_lt this hq2) (lt_irrefl _)
  generalize Filter.limsup (fun t => ((G t : ℝ) : EReal)) Filter.atTop = Gb at claim ⊢
  induction Gb using EReal.rec with
  | bot =>
    exfalso
    have hq : ε * (-V / ε) = B + V * ((gs - B / V - 1) - gs) := by
      field_simp
      ring
    have h1 := claim (gs - B / V - 1) (-V / ε) hq (EReal.bot_lt_coe _)
    have h2 : (0 : EReal) ≤ ((-V / ε : ℝ) : EReal) := hM0.trans h1
    have h3 : (0 : ℝ) ≤ -V / ε := by exact_mod_cast h2
    have : -V / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    linarith
  | top =>
    rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos hV, EReal.coe_add_top]
    exact le_top
  | coe r =>
    have h1 := claim (r + 1) ((B + V * ((r + 1) - gs)) / ε)
      (mul_div_cancel₀ _ hε.ne') (EReal.coe_lt_coe_iff.2 (by linarith))
    have hMtop : Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hMbot : Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop ≠ ⊥ := by
      intro h
      rw [h] at hM0
      exact absurd hM0 (by simp)
    generalize hMdef : Filter.limsup (fun t => ((u t : ℝ) : EReal)) Filter.atTop = M at *
    have hM : ((M.toReal : ℝ) : EReal) = M := EReal.coe_toReal hMtop hMbot
    have hreal : ε * M.toReal ≤ B + V * (r - gs) := by
      by_contra hlt
      push_neg at hlt
      have hη : 0 < (ε * M.toReal - (B + V * (r - gs))) / (2 * V) :=
        div_pos (by linarith) (by positivity)
      set η := (ε * M.toReal - (B + V * (r - gs))) / (2 * V) with hηdef
      have hVη : V * η = (ε * M.toReal - (B + V * (r - gs))) / 2 := by
        rw [hηdef]; field_simp
      have h2 := claim (r + η) ((B + V * ((r + η) - gs)) / ε)
        (mul_div_cancel₀ _ hε.ne') (EReal.coe_lt_coe_iff.2 (by linarith))
      rw [← hM] at h2
      have h3 : M.toReal ≤ (B + V * ((r + η) - gs)) / ε := by exact_mod_cast h2
      rw [le_div_iff₀ hε] at h3
      nlinarith
    rw [← hM]
    have : ((ε * M.toReal : ℝ) : EReal) ≤ ((B + V * (r - gs) : ℝ) : EReal) := by
      exact_mod_cast hreal
    push_cast at this
    exact this

lemma h24_part2 (r : ℕ → ℝ) (a C' : ℝ) (hK : ∀ t : ℕ, 1 ≤ t → a - C' / t ≤ r t) :
    ((a : ℝ) : EReal) ≤ Filter.liminf (fun t => ((r t : ℝ) : EReal)) Filter.atTop := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hc : c < a := by exact_mod_cast h2
  have hC : Filter.Tendsto (fun t : ℕ => C' / (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C'
  have e1 := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) h1
  have e2 : ∀ᶠ t : ℕ in Filter.atTop, C' / (t : ℝ) < a - c :=
    hC.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ t : ℕ in Filter.atTop, 1 ≤ t := Filter.eventually_ge_atTop 1
  obtain ⟨t, ht1, ht2, ht3⟩ := (e1.and_eventually (e2.and e3)).exists
  have h1' : r t < c := by exact_mod_cast ht1
  have := hK t ht3
  linarith


lemma h24_goal_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω
          - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)) :
    ((ε : EReal) *
        Filter.limsup
          (fun t : ℕ =>
            (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
          Filter.atTop
      ≤ (B : EReal) + (V : EReal) *
          (Filter.limsup
            (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P : ℝ) : EReal))
            Filter.atTop - (gstar : EReal))) ∧
    (((gstar - B / V : ℝ) : EReal) ≤
      Filter.liminf
        (fun t : ℕ =>
          ((g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P) : ℝ) : EReal))
        Filter.atTop) := by
  have hm : ∀ t, MeasurableSpace.comap (U t) inferInstance ≤ mΩ :=
    fun t => h24_comap_le (U t) (hMeasU t)
  have hSU : ∀ t, Integrable (fun ω => ∑ i : Fin N, U t ω i) P :=
    fun t => integrable_finset_sum _ (fun i _ => hIntegU t i)
  have step : ∀ t : ℕ, (∫ ω, L (U (t+1) ω) ∂P - ∫ ω, L (U t ω) ∂P) - V * ∫ ω, g (R t ω) ∂P
      ≤ B - ε * ∑ i : Fin N, ∫ ω, U t ω i ∂P - V * gstar := by
    intro t
    have hcg : Integrable (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) P :=
      integrable_condExp
    have hint1 : Integrable (fun ω => drift P L U t ω
        - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω) P :=
      (h24_integrable_drift L U t).sub (hcg.const_mul V)
    have hint2 : Integrable (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar) P :=
      ((integrable_const B).sub ((hSU t).const_mul ε)).sub (integrable_const _)
    have hle := integral_mono_ae hint1 hint2 (hdrift t)
    have e1 : ∫ ω, (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω ∂P
        = ∫ ω, g (R t ω) ∂P := integral_condExp (hm t)
    have eL : ∫ ω, (drift P L U t ω
        - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω) ∂P
        = (∫ ω, L (U (t+1) ω) ∂P - ∫ ω, L (U t ω) ∂P) - V * ∫ ω, g (R t ω) ∂P := by
      rw [integral_sub (h24_integrable_drift L U t) (hcg.const_mul V), integral_const_mul, e1,
        h24_integral_drift L U hMeasU hIntegL t]
    have eR : ∫ ω, (B - ε * ∑ i : Fin N, U t ω i - V * gstar) ∂P
        = B - ε * ∑ i : Fin N, ∫ ω, U t ω i ∂P - V * gstar := by
      have i0 : Integrable (fun _ : Ω => B) P := integrable_const B
      have i2 : Integrable (fun ω => ε * ∑ i : Fin N, U t ω i) P := (hSU t).const_mul ε
      have i1 : Integrable (fun ω => B - ε * ∑ i : Fin N, U t ω i) P := i0.sub i2
      have i3 : Integrable (fun _ : Ω => V * gstar) P := integrable_const _
      rw [integral_sub i1 i3, integral_sub i0 i2, integral_const_mul,
        integral_finset_sum _ (fun i _ => hIntegU t i)]
      simp
    rw [eL, eR] at hle
    exact hle
  set C : ℝ := ∫ ω, L (U 0 ω) ∂P with hCdef
  have hL0 : ∀ t, 0 ≤ ∫ ω, L (U t ω) ∂P := fun t => integral_nonneg (fun ω => hLnn _)
  have hUi : ∀ τ, 0 ≤ ∑ i : Fin N, ∫ ω, U τ ω i ∂P :=
    fun τ => Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => hUnn _ _ _))
  have hsum : ∀ t : ℕ, ∫ ω, L (U t ω) ∂P - C
      - V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P
      ≤ t * B - ε * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P - t * V * gstar := by
    intro t
    have h1 := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.range t) => step τ)
    have hl : ∑ τ ∈ Finset.range t, ((∫ ω, L (U (τ+1) ω) ∂P - ∫ ω, L (U τ ω) ∂P)
        - V * ∫ ω, g (R τ ω) ∂P)
        = ∫ ω, L (U t ω) ∂P - C - V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P := by
      rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun τ => ∫ ω, L (U τ ω) ∂P),
        ← Finset.mul_sum]
    have hr : ∑ τ ∈ Finset.range t, (B - ε * ∑ i : Fin N, ∫ ω, U τ ω i ∂P - V * gstar)
        = t * B - ε * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P - t * V * gstar := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring
    rw [hl, hr] at h1
    exact h1
  have hSu : ∀ t : ℕ, 0 ≤ ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P :=
    fun t => Finset.sum_nonneg (fun τ _ => hUi τ)
  constructor
  · refine h24_part1 (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P)
      (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P)
      ε V B gstar C hε hV (fun t => mul_nonneg (by positivity) (hSu t)) ?_
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have h1 := hsum t
    have h2 := hL0 t
    have h3 : ε * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P
        ≤ t * B - t * V * gstar + V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P + C := by
      linarith
    have h4 : (1 / (t : ℝ)) * (ε * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P)
        ≤ (1 / (t : ℝ)) * (t * B - t * V * gstar
          + V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P + C) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ε * ((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P)
        = (1 / (t : ℝ)) * (ε * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P) := by ring
      _ ≤ _ := h4
      _ = _ := by field_simp
  · refine h24_part2 (fun t : ℕ =>
        g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P))
      (gstar - B / V) (C / V) ?_
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have h1 := hsum t
    have h2 := hL0 t
    have h3 : t * V * gstar - t * B - C
        ≤ V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P := by
      have := mul_nonneg hε.le (hSu t)
      linarith
    have hG : gstar - B / V - C / V / t
        ≤ (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P := by
      have h5 : gstar - B / V - C / V / t
          = (1 / (V * t)) * (t * V * gstar - t * B - C) := by
        field_simp
      rw [h5]
      calc (1 / (V * t)) * (t * V * gstar - t * B - C)
          ≤ (1 / (V * t)) * (V * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by field_simp
    refine hG.trans ?_
    have hj : ∀ τ, ∫ ω, g (R τ ω) ∂P ≤ g (fun k => ∫ ω, R τ ω k ∂P) :=
      fun τ => h24_jensen_vec g hgConcave (R τ) (hIntegR τ) (hIntegG τ)
    calc (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P
        ≤ (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, g (fun k => ∫ ω, R τ ω k ∂P) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun τ _ => hj τ)) (by positivity)
      _ ≤ _ := h24_jensen_avg g hgConcave (fun τ k => ∫ ω, R τ ω k ∂P) t ht

end NetworkControl.UtilityFairness

open NetworkControl.UtilityFairness
open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω
          - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)) :
    ((ε : EReal) *
        Filter.limsup
          (fun t : ℕ =>
            (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
          Filter.atTop
      ≤ (B : EReal) + (V : EReal) *
          (Filter.limsup
            (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P : ℝ) : EReal))
            Filter.atTop - (gstar : EReal))) ∧
    (((gstar - B / V : ℝ) : EReal) ≤
      Filter.liminf
        (fun t : ℕ =>
          ((g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P) : ℝ) : EReal))
        Filter.atTop) := by
  exact h24_goal_core L hLnn U R g gstar hgConcave V ε B hV hε hB hUnn hMeasU hIntegL hIntegG hIntegU hIntegR hdrift
