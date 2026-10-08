-- Prove2me | solution 1 for IDivGeom.IPFP.eq_3_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:27:27.012122+00:00
-- url     : https://prove2.me/submissions/45d5fbc0-04a9-4544-a45d-91256327f842

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

set_option autoImplicit false

namespace DcadKL

open Real Filter Topology

/-- Per-coordinate derivative of `t ↦ m_t * log (m_t / r)` at `0`, where `m_t = q + t (p - q)`. -/
lemma term_hasDeriv (p q r : ℝ) (hq : 0 < q) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (q + t * (p - q)) * Real.log ((q + t * (p - q)) / r))
      ((p - q) * (Real.log (q / r) + 1)) 0 := by
  have hm : HasDerivAt (fun t : ℝ => q + t * (p - q)) (p - q) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (p - q)).const_add q
  have hne : (q + (0:ℝ) * (p - q)) / r ≠ 0 := by
    simp; exact ⟨hq.ne', hr.ne'⟩
  have hl := (hm.div_const r).log hne
  have hq' := hq.ne'
  have hr' := hr.ne'
  refine (hm.fun_mul hl).congr_deriv ?_
  rw [zero_mul, add_zero, show q * ((p - q) / r / (q / r)) = p - q by field_simp]
  ring

lemma core {X : Type*} [Fintype X] (p q r : X → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hr0 : ∀ x, 0 ≤ r x)
    (hpr : ∀ x, r x = 0 → p x = 0) (hqr : ∀ x, r x = 0 → q x = 0)
    (hsp : ∑ x, p x = 1) (hsq : ∑ x, q x = 1)
    (hmin : ∀ t : ℝ, (∀ x, 0 ≤ q x + t * (p x - q x)) →
      ∑ x, q x * Real.log (q x / r x) ≤
        ∑ x, (q x + t * (p x - q x)) * Real.log ((q x + t * (p x - q x)) / r x)) :
    (∀ x, q x = 0 → p x = 0) ∧
      ∑ x, p x * Real.log (q x / r x) = ∑ x, q x * Real.log (q x / r x) := by
  set G : ℝ → ℝ := fun t =>
    ∑ x, (q x + t * (p x - q x)) * Real.log ((q x + t * (p x - q x)) / r x) with hG
  have hG0 : G 0 = ∑ x, q x * Real.log (q x / r x) := by simp [hG]
  -- Part (i): p ≪ q
  have part1 : ∀ x, q x = 0 → p x = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x0, hqx0, hpx0⟩ := hcon
    have hpx0' : 0 < p x0 := lt_of_le_of_ne (hp0 x0) (Ne.symm hpx0)
    set S := Finset.univ.filter (fun x => 0 < q x) with hS
    set T := Finset.univ.filter (fun x => ¬ 0 < q x) with hT
    set A : ℝ → ℝ := fun t =>
      ∑ x ∈ S, (q x + t * (p x - q x)) * Real.log ((q x + t * (p x - q x)) / r x) with hA
    set a : ℝ := ∑ x ∈ T, p x with ha
    set b : ℝ := ∑ x ∈ T, p x * Real.log (p x / r x) with hb
    have hx0T : x0 ∈ T := by simp [hT, hqx0]
    have ha_pos : 0 < a := by
      have : p x0 ≤ a := Finset.single_le_sum (fun x _ => hp0 x) hx0T
      linarith
    have hAder : HasDerivAt A (∑ x ∈ S, (p x - q x) * (Real.log (q x / r x) + 1)) 0 := by
      apply HasDerivAt.fun_sum
      intro x hx
      have hqx : 0 < q x := (Finset.mem_filter.1 hx).2
      have hrx : 0 < r x := by
        rcases (hr0 x).lt_or_eq with h | h
        · exact h
        · exact absurd (hqr x h.symm) hqx.ne'
      exact term_hasDeriv (p x) (q x) (r x) hqx hrx
    have hslope := (hasDerivAt_iff_tendsto_slope.1 hAder).mono_left
      (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
    have hBt : ∀ t : ℝ, 0 < t →
        ∑ x ∈ T, (q x + t * (p x - q x)) * Real.log ((q x + t * (p x - q x)) / r x)
          = t * (a * Real.log t + b) := by
      intro t ht
      rw [ha, hb, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hqx : q x = 0 := le_antisymm (not_lt.1 (Finset.mem_filter.1 hx).2) (hq0 x)
      rw [hqx]
      rcases (hp0 x).lt_or_eq with hpx | hpx
      · have hrx : 0 < r x := by
          rcases (hr0 x).lt_or_eq with h | h
          · exact h
          · exact absurd (hpr x h.symm) hpx.ne'
        have : (0 + t * (p x - 0)) / r x = t * (p x / r x) := by ring
        rw [this, Real.log_mul ht.ne' (div_pos hpx hrx).ne']
        ring
      · rw [← hpx]; simp
    have hB0 : ∑ x ∈ T, q x * Real.log (q x / r x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hqx : q x = 0 := le_antisymm (not_lt.1 (Finset.mem_filter.1 hx).2) (hq0 x)
      simp [hqx]
    have hsplit : ∀ t, G t = A t +
        ∑ x ∈ T, (q x + t * (p x - q x)) * Real.log ((q x + t * (p x - q x)) / r x) := by
      intro t
      simp only [hG, hA, hS, hT]
      rw [Finset.sum_filter_add_sum_filter_not]
    have hA0 : A 0 = G 0 := by
      rw [hsplit 0]
      simp only [zero_mul, add_zero] at hB0 ⊢
      rw [hB0, add_zero]
    have hkey : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ slope A 0 t + (a * Real.log t + b) := by
      intro t ht0 ht1
      have hm : ∀ x, 0 ≤ q x + t * (p x - q x) := by
        intro x
        have := hp0 x; have := hq0 x
        nlinarith
      have hle := hmin t hm
      rw [← hG0] at hle
      have hGt : G t = A t + t * (a * Real.log t + b) := by rw [hsplit t, hBt t ht0]
      rw [slope_def_field, sub_zero]
      have : (A t - A 0) / t + (a * Real.log t + b) = (G t - G 0) / t := by
        rw [hGt, hA0]; field_simp; ring
      rw [this]
      apply div_nonneg _ ht0.le
      have : G 0 ≤ G t := hle
      linarith
    have hlogt : Tendsto (fun t => a * Real.log t + b) (𝓝[>] (0:ℝ)) atBot := by
      apply tendsto_atBot_add_const_right
      exact Tendsto.const_mul_atBot ha_pos Real.tendsto_log_nhdsGT_zero
    have hsum := hslope.add_atBot hlogt
    have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), slope A 0 t + (a * Real.log t + b) < 0 :=
      hsum.eventually (eventually_lt_atBot 0)
    have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨t, h1, h2⟩ := (hev1.and hev2).exists
    have := hkey t h2.1 h2.2
    linarith
  refine ⟨part1, ?_⟩
  -- Part (ii): first-order condition
  have hder : HasDerivAt G (∑ x, (p x - q x) * (Real.log (q x / r x) + 1)) 0 := by
    apply HasDerivAt.fun_sum
    intro x _
    rcases (hq0 x).lt_or_eq with hqx | hqx
    · have hrx : 0 < r x := by
        rcases (hr0 x).lt_or_eq with h | h
        · exact h
        · exact absurd (hqr x h.symm) hqx.ne'
      exact term_hasDeriv (p x) (q x) (r x) hqx hrx
    · have hpx := part1 x hqx.symm
      rw [← hqx, hpx]
      simpa using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hloc : IsLocalMin G 0 := by
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ x, 0 ≤ q x + t * (p x - q x) := by
      rw [Filter.eventually_all]
      intro x
      rcases (hq0 x).lt_or_eq with hqx | hqx
      · have hc : Tendsto (fun t : ℝ => q x + t * (p x - q x)) (𝓝 0) (𝓝 (q x)) := by
          have hcont : Continuous (fun t : ℝ => q x + t * (p x - q x)) := by fun_prop
          exact hcont.tendsto' 0 (q x) (by simp)
        filter_upwards [hc.eventually (lt_mem_nhds hqx)] with t ht
        exact ht.le
      · have hpx := part1 x hqx.symm
        filter_upwards with t
        rw [← hqx, hpx]; simp
    filter_upwards [hev] with t ht
    rw [hG0]
    exact hmin t ht
  have h0 := hloc.hasDerivAt_eq_zero hder
  have hsplit2 : ∑ x, (p x - q x) * (Real.log (q x / r x) + 1)
      = (∑ x, p x * Real.log (q x / r x) - ∑ x, q x * Real.log (q x / r x))
        + (∑ x, p x - ∑ x, q x) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit2, hsp, hsq] at h0
  linarith

end DcadKL

namespace DcadKL

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

lemma real_eq_sum (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) :
    μ.real s = ∑ x, s.indicator (fun y => μ.real {y}) x := by
  classical
  have hs : s = ((Finset.univ.filter (· ∈ s) : Finset X) : Set X) := by ext; simp
  conv_lhs => rw [hs]
  rw [← sum_measureReal_singleton, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s <;> simp [hx]

lemma sum_real_one (μ : Measure X) [IsProbabilityMeasure μ] : ∑ x, μ.real {x} = 1 := by
  rw [sum_measureReal_singleton]; simp

lemma ac_iff (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ ≪ ν ↔ ∀ x, ν.real {x} = 0 → μ.real {x} = 0 := by
  constructor
  · intro h x hx
    rw [measureReal_eq_zero_iff] at hx ⊢
    exact h hx
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s _ hs => ?_
    have hsr : ν.real s = 0 := by rw [measureReal_eq_zero_iff]; exact hs
    have : μ.real s = 0 := by
      rw [real_eq_sum]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx]
        apply h
        apply le_antisymm _ measureReal_nonneg
        rw [← hsr]
        exact measureReal_mono (Set.singleton_subset_iff.2 hx)
      · simp [hx]
    rwa [measureReal_eq_zero_iff] at this

lemma kl_toReal (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ≪ ν) :
    klDiv μ ν ≠ ⊤ ∧
      (klDiv μ ν).toReal = ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  have hint : Integrable (llr μ ν) μ := Integrable.of_finite
  refine ⟨klDiv_ne_top h hint, ?_⟩
  rw [toReal_klDiv_of_measure_eq h (by simp), integral_fintype (hf := hint)]
  apply Finset.sum_congr rfl
  intro x _
  rw [smul_eq_mul]
  by_cases hμx : μ.real {x} = 0
  · simp [hμx]
  have hνx : ν.real {x} ≠ 0 := fun h0 => hμx ((ac_iff μ ν).1 h x h0)
  have key : μ.rnDeriv ν x * ν {x} = μ {x} := by
    rw [← lintegral_singleton, Measure.setLIntegral_rnDeriv' h (measurableSet_singleton x)]
  have key' : (μ.rnDeriv ν x).toReal * ν.real {x} = μ.real {x} := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_mul, key]
  have : (μ.rnDeriv ν x).toReal = μ.real {x} / ν.real {x} := by
    rw [eq_div_iff hνx, key']
  rw [llr, this]

lemma pyth (L : Set (Measure X)) (hL : IDivGeom.IPFP.IsLinearPD L)
    (r : Measure X) [IsProbabilityMeasure r] (q : Measure X)
    (hq : IDivGeom.IPFP.IsIProjection r L q) (p : Measure X) (hp : p ∈ L) :
    klDiv p r = klDiv p q + klDiv q r := by
  obtain ⟨hqL, hqfin, hqmin⟩ := hq
  haveI : IsProbabilityMeasure q := hL.1 q hqL
  haveI : IsProbabilityMeasure p := hL.1 p hp
  have hqr : q ≪ r := by
    by_contra h
    exact hqfin (klDiv_of_not_ac h)
  by_cases hpr : p ≪ r
  swap
  · have hpq : ¬ p ≪ q := fun h => hpr (h.trans hqr)
    rw [klDiv_of_not_ac hpr, klDiv_of_not_ac hpq, top_add]
  have hmin' : ∀ t : ℝ, (∀ x, 0 ≤ q.real {x} + t * (p.real {x} - q.real {x})) →
      ∑ x, q.real {x} * Real.log (q.real {x} / r.real {x}) ≤
        ∑ x, (q.real {x} + t * (p.real {x} - q.real {x})) *
          Real.log ((q.real {x} + t * (p.real {x} - q.real {x})) / r.real {x}) := by
    intro t ht
    set w : X → ℝ := fun x => q.real {x} + t * (p.real {x} - q.real {x}) with hw
    have hw1 : ∑ x, w x = 1 := by
      simp only [hw, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        sum_real_one, sub_self, mul_zero, add_zero]
    set M : Measure X := Measure.sum (fun x => ENNReal.ofReal (w x) • Measure.dirac x) with hM
    have hMs : ∀ s : Set X, M.real s = ∑ x, s.indicator w x := by
      intro s
      have hs : MeasurableSet s := (Set.toFinite s).measurableSet
      rw [measureReal_def, hM, Measure.sum_apply _ hs, tsum_fintype, ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro x _
        have hw0 : 0 ≤ w x := ht x
        by_cases hx : x ∈ s <;>
          simp [hx, Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.toReal_ofReal hw0]
      · intro x _
        by_cases hx : x ∈ s <;> simp [hx, Measure.smul_apply, Measure.dirac_apply' _ hs]
    haveI : IsProbabilityMeasure M := by
      constructor
      rw [hM, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => ht x), hw1, ENNReal.ofReal_one]
    have hMx : ∀ y, M.real {y} = w y := by
      intro y
      rw [hMs, Finset.sum_eq_single y]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have hML : M ∈ L := by
      refine hL.2 p hp q hqL t M inferInstance (fun s _ => ?_)
      rw [hMs, real_eq_sum p s, real_eq_sum q s, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx, hw]; ring
      · simp [hx]
    have hMr : M ≪ r := (ac_iff M r).2 (fun x hx => by
      rw [hMx]
      simp [hw, (ac_iff p r).1 hpr x hx, (ac_iff q r).1 hqr x hx])
    have h1 := hqmin M hML
    obtain ⟨hMfin, hMval⟩ := kl_toReal M r hMr
    obtain ⟨_, hqval⟩ := kl_toReal q r hqr
    have h2 := ENNReal.toReal_mono hMfin h1
    rw [hqval, hMval] at h2
    simp only [hMx] at h2
    exact h2
  obtain ⟨hpq0, hlin⟩ := core (fun x => p.real {x}) (fun x => q.real {x}) (fun x => r.real {x})
    (fun x => measureReal_nonneg) (fun x => measureReal_nonneg) (fun x => measureReal_nonneg)
    ((ac_iff p r).1 hpr) ((ac_iff q r).1 hqr) (sum_real_one p) (sum_real_one q) hmin'
  have hpq : p ≪ q := (ac_iff p q).2 hpq0
  obtain ⟨f1, v1⟩ := kl_toReal p r hpr
  obtain ⟨f2, v2⟩ := kl_toReal p q hpq
  obtain ⟨f3, v3⟩ := kl_toReal q r hqr
  rw [← ENNReal.toReal_eq_toReal_iff' f1 (ENNReal.add_ne_top.2 ⟨f2, f3⟩),
    ENNReal.toReal_add f2 f3, v1, v2, v3]
  rw [← hlin, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hpx : p.real {x} = 0
  · simp [hpx]
  have hqx : q.real {x} ≠ 0 := fun h => hpx (hpq0 x h)
  have hrx : r.real {x} ≠ 0 := fun h => hqx ((ac_iff q r).1 hqr x h)
  rw [← mul_add, ← Real.log_mul (div_ne_zero hpx hqx) (div_ne_zero hqx hrx)]
  congr 2
  field_simp

end DcadKL

open MeasureTheory InformationTheory IDivGeom.IPFP in
theorem solution {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (hne : (⋂ i, ℰ i).Nonempty)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ⋂ i, ℰ i, P ≪ R)
    (Qs : ℕ → Measure X) (hQs : IsCyclicIProjSeq hk ℰ R Qs)
    (Q : Measure X) (hQ : IsIProjection R (⋂ i, ℰ i) Q) :
    ∀ n, 0 < n →
      klDiv Q R = klDiv Q (Qs n) +
        ∑ i ∈ Finset.range n, klDiv (Qs (i + 1)) (Qs i) := by
  have hQmem : ∀ i, Q ∈ ℰ i := Set.mem_iInter.1 hQ.1
  have hprob : ∀ m, IsProbabilityMeasure (Qs m) := by
    intro m
    cases m with
    | zero => rw [hQs.1]; infer_instance
    | succ m => exact (hlin _).1 _ (hQs.2 m).1
  have key : ∀ n : ℕ, klDiv Q R = klDiv Q (Qs n) +
      ∑ i ∈ Finset.range n, klDiv (Qs (i + 1)) (Qs i) := by
    intro n
    induction n with
    | zero => simp [hQs.1]
    | succ m ih =>
      haveI := hprob m
      rw [ih, DcadKL.pyth (ℰ (cyc k m hk)) (hlin _) (Qs m) (Qs (m + 1)) (hQs.2 m) Q (hQmem _),
        Finset.sum_range_succ]
      ring
  exact fun n _ => key n
