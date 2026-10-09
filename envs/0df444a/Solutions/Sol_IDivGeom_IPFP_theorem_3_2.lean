-- Prove2me | solution 1 for IDivGeom.IPFP.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:18:31.648086+00:00
-- url     : https://prove2.me/submissions/f4cfb654-daa7-4755-be3e-e69491f3412d

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

namespace DcadKL

lemma linear_iInter {X : Type*} [MeasurableSpace X] {k : ℕ} (hk : 0 < k)
    (ℰ : Fin k → Set (Measure X)) (hlin : ∀ i, IDivGeom.IPFP.IsLinearPD (ℰ i)) :
    IDivGeom.IPFP.IsLinearPD (⋂ i, ℰ i) := by
  refine ⟨fun P hP => (hlin ⟨0, hk⟩).1 P (Set.mem_iInter.1 hP _), ?_⟩
  intro P hP P' hP' α M hM hs
  exact Set.mem_iInter.2 fun i =>
    (hlin i).2 P (Set.mem_iInter.1 hP i) P' (Set.mem_iInter.1 hP' i) α M hM hs

end DcadKL

namespace IPFPc

open Real Filter Topology IDivGeom.IPFP DcadKL

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

lemma exists_meas (w : X → ℝ) (h0 : ∀ x, 0 ≤ w x) (h1 : ∑ x, w x = 1) :
    ∃ M : Measure X, IsProbabilityMeasure M ∧ ∀ x, M.real {x} = w x := by
  set M : Measure X := Measure.sum (fun x => ENNReal.ofReal (w x) • Measure.dirac x) with hM
  have hMs : ∀ s : Set X, M.real s = ∑ x, s.indicator w x := by
    intro s
    have hs : MeasurableSet s := (Set.toFinite s).measurableSet
    rw [measureReal_def, hM, Measure.sum_apply _ hs, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro x _
      have hw0 : 0 ≤ w x := h0 x
      by_cases hx : x ∈ s <;>
        simp [hx, Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.toReal_ofReal hw0]
    · intro x _
      by_cases hx : x ∈ s <;> simp [hx, Measure.smul_apply, Measure.dirac_apply' _ hs]
  refine ⟨M, ?_, fun y => ?_⟩
  · constructor
    rw [hM, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => h0 x), h1, ENNReal.ofReal_one]
  · rw [hMs, Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

lemma lin_mem (L : Set (Measure X)) (hL : IsLinearPD L) (P P' : Measure X) (hP : P ∈ L)
    (hP' : P' ∈ L) (α : ℝ) (M : Measure X) [IsProbabilityMeasure M]
    (hM : ∀ x, M.real {x} = α * P.real {x} + (1 - α) * P'.real {x}) : M ∈ L := by
  haveI := hL.1 P hP
  haveI := hL.1 P' hP'
  refine hL.2 P hP P' hP' α M inferInstance (fun s _ => ?_)
  rw [real_eq_sum M s, real_eq_sum P s, real_eq_sum P' s, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, hM]
  · simp [hx]

def InL (L : Set (Measure X)) (w : X → ℝ) : Prop := ∃ P ∈ L, ∀ x, P.real {x} = w x

lemma InL.nonneg {L : Set (Measure X)} {w : X → ℝ} (h : InL L w) (x : X) : 0 ≤ w x := by
  obtain ⟨P, _, hP⟩ := h
  rw [← hP]
  exact measureReal_nonneg

lemma InL.sum {L : Set (Measure X)} (hL : IsLinearPD L) {w : X → ℝ} (h : InL L w) :
    ∑ x, w x = 1 := by
  obtain ⟨P, hPL, hP⟩ := h
  haveI := hL.1 P hPL
  simp only [← hP]
  exact sum_real_one P

lemma InL.le_one {L : Set (Measure X)} (hL : IsLinearPD L) {w : X → ℝ} (h : InL L w) (x : X) :
    w x ≤ 1 := by
  rw [← h.sum hL]
  exact Finset.single_le_sum (fun y _ => h.nonneg y) (Finset.mem_univ x)

lemma lin_vec {L : Set (Measure X)} (hL : IsLinearPD L) {p p' : X → ℝ} (hp : InL L p)
    (hp' : InL L p') (α : ℝ) (h0 : ∀ x, 0 ≤ α * p x + (1 - α) * p' x) :
    InL L (fun x => α * p x + (1 - α) * p' x) := by
  have hs : ∑ x, (α * p x + (1 - α) * p' x) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.sum hL, hp'.sum hL]
    ring
  obtain ⟨P, hPL, hP⟩ := hp
  obtain ⟨P', hPL', hP'⟩ := hp'
  obtain ⟨M, hMp, hMx⟩ := exists_meas _ h0 hs
  haveI := hMp
  exact ⟨M, lin_mem L hL P P' hPL hPL' α M (fun x => by rw [hMx, hP, hP']), hMx⟩

lemma scale {L : Set (Measure X)} (hL : IsLinearPD L) {ps v : X → ℝ} (hps : InL L ps)
    {ε : ℝ} (hε : 0 < ε) (h : InL L (fun x => ps x + ε * v x)) {ε' : ℝ} (h0 : 0 ≤ ε')
    (h1 : ε' ≤ ε) : InL L (fun x => ps x + ε' * v x) := by
  have ha : 0 ≤ ε' / ε := div_nonneg h0 hε.le
  have hb : 0 ≤ 1 - ε' / ε := by rw [sub_nonneg, div_le_one hε]; exact h1
  have := lin_vec hL h hps (ε' / ε) (fun x =>
    add_nonneg (mul_nonneg ha (h.nonneg x)) (mul_nonneg hb (hps.nonneg x)))
  have e : (fun x => ε' / ε * (ps x + ε * v x) + (1 - ε' / ε) * ps x) =
      (fun x => ps x + ε' * v x) := by
    funext x
    field_simp
    ring
  rwa [e] at this

lemma exists_max_supp {L : Set (Measure X)} (hL : IsLinearPD L) (hne : L.Nonempty) :
    ∃ ps, InL L ps ∧ ∀ p, InL L p → ∀ x, ps x = 0 → p x = 0 := by
  classical
  let S : Set (Finset X) :=
    (fun p : X → ℝ => Finset.univ.filter (fun x => 0 < p x)) '' {p | InL L p}
  have hSne : S.Nonempty := by
    obtain ⟨P, hP⟩ := hne
    exact ⟨_, ⟨fun x => P.real {x}, ⟨P, hP, fun x => rfl⟩, rfl⟩⟩
  obtain ⟨s, ⟨ps, hps, rfl⟩, hmax⟩ := Set.exists_max_image S Finset.card (Set.toFinite S) hSne
  refine ⟨ps, hps, fun p hp x hx => ?_⟩
  by_contra hpx
  have hpx' : 0 < p x := lt_of_le_of_ne (hp.nonneg x) (Ne.symm hpx)
  have hmid := lin_vec hL hp hps (1 / 2) (fun y => by
    have := hp.nonneg y
    have := hps.nonneg y
    positivity)
  have hle := hmax _ ⟨_, hmid, rfl⟩
  have hsub : Finset.univ.filter (fun y => 0 < ps y) ⊂
      Finset.univ.filter (fun y => 0 < (1 / 2 * p y + (1 - 1 / 2) * ps y)) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx]
        linarith
      · simp [hx]
    · intro y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hy
      have := hp.nonneg y
      linarith
  exact absurd (Finset.card_lt_card hsub) (not_lt.2 hle)

lemma closedL {L : Set (Measure X)} (hL : IsLinearPD L) (u : ℕ → X → ℝ)
    (hu : ∀ n, InL L (u n)) (m : X → ℝ) (hm : Tendsto u atTop (𝓝 m))
    (M : Measure X) [IsProbabilityMeasure M] (hM : ∀ x, M.real {x} = m x) : M ∈ L := by
  classical
  have hne : L.Nonempty := by
    obtain ⟨P, hP, _⟩ := hu 0
    exact ⟨P, hP⟩
  obtain ⟨ps, hps, hsupp⟩ := exists_max_supp hL hne
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ x, ps x ≠ 0 → δ ≤ ps x := by
    by_cases hU : (Finset.univ.filter (fun x => ps x ≠ 0)).Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image _ ps hU
      refine ⟨ps x0, lt_of_le_of_ne (hps.nonneg x0) (Ne.symm (Finset.mem_filter.1 hx0).2),
        fun x hx => hmin x (by simp [hx])⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, by simp [hx]⟩ hU⟩
  let V : Submodule ℝ (X → ℝ) := Submodule.span ℝ {v | ∃ p, InL L p ∧ v = p - ps}
  have key : ∀ v ∈ V, ∃ ε > 0, InL L (fun x => ps x + ε * v x) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨p, hp, rfl⟩ := hv
      refine ⟨1, one_pos, ?_⟩
      have e : (fun x => ps x + 1 * (p - ps) x) = p := by
        funext x
        simp
      rw [e]
      exact hp
    | zero =>
      refine ⟨1, one_pos, ?_⟩
      have e : (fun x => ps x + 1 * (0 : X → ℝ) x) = ps := by
        funext x
        simp
      rw [e]
      exact hps
    | add v w _ _ hv hw =>
      obtain ⟨ε1, h1, hv1⟩ := hv
      obtain ⟨ε2, h2, hw2⟩ := hw
      have he : 0 < min ε1 ε2 := lt_min h1 h2
      have hv' := scale hL hps h1 hv1 he.le (min_le_left _ _)
      have hw' := scale hL hps h2 hw2 he.le (min_le_right _ _)
      have hmid := lin_vec hL hv' hw' (1 / 2) (fun x => by
        have := hv'.nonneg x
        have := hw'.nonneg x
        positivity)
      refine ⟨min ε1 ε2 / 2, half_pos he, ?_⟩
      have e : (fun x => 1 / 2 * (ps x + min ε1 ε2 * v x) + (1 - 1 / 2) *
          (ps x + min ε1 ε2 * w x)) = (fun x => ps x + min ε1 ε2 / 2 * (v + w) x) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rwa [e] at hmid
    | smul c v _ hv =>
      obtain ⟨ε, hε, hvε⟩ := hv
      rcases lt_trichotomy c 0 with hc | hc | hc
      · refine ⟨δ * ε / (-c), div_pos (mul_pos hδ hε) (neg_pos.2 hc), ?_⟩
        have hmid := lin_vec hL hvε hps (-δ) (fun x => by
          by_cases hx : ps x = 0
          · have := hsupp _ hvε x hx
            rw [hx] at this ⊢
            nlinarith
          · have h1 := hvε.le_one hL x
            have h2 := hδle x hx
            nlinarith)
        have e : (fun x => -δ * (ps x + ε * v x) + (1 - -δ) * ps x) =
            (fun x => ps x + δ * ε / (-c) * (c • v) x) := by
          funext x
          have hc0 : c ≠ 0 := hc.ne
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rwa [e] at hmid
      · refine ⟨1, one_pos, ?_⟩
        have e : (fun x => ps x + 1 * (c • v) x) = ps := by
          funext x
          simp [hc]
        rw [e]
        exact hps
      · refine ⟨ε / c, div_pos hε hc, ?_⟩
        have e : (fun x => ps x + ε / c * (c • v) x) = (fun x => ps x + ε * v x) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
        rw [e]
        exact hvε
  have hmV : m - ps ∈ V := by
    have hcl : IsClosed (V : Set (X → ℝ)) := V.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto (hm.sub tendsto_const_nhds) (Eventually.of_forall fun n => ?_)
    exact Submodule.subset_span ⟨u n, hu n, rfl⟩
  obtain ⟨ε, hε, hu'⟩ := key _ hmV
  obtain ⟨U, hUL, hUx⟩ := hu'
  obtain ⟨Ps, hPsL, hPsx⟩ := hps
  refine lin_mem L hL U Ps hUL hPsL (1 / ε) M (fun x => ?_)
  rw [hUx, hPsx, hM]
  simp only [Pi.sub_apply]
  field_simp
  ring

lemma bw (Ps : ℕ → Measure X) (hPs : ∀ n, IsProbabilityMeasure (Ps n)) :
    ∃ (M : Measure X) (φ : ℕ → ℕ), IsProbabilityMeasure M ∧ StrictMono φ ∧
      ∀ x, Tendsto (fun j => (Ps (φ j)).real {x}) atTop (𝓝 (M.real {x})) := by
  set u : ℕ → X → ℝ := fun n x => (Ps n).real {x} with hu_def
  have hK : IsCompact (Set.pi Set.univ (fun _ : X => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hu : ∀ n, u n ∈ Set.pi Set.univ (fun _ : X => Set.Icc (0:ℝ) 1) := by
    intro n x _
    haveI := hPs n
    refine ⟨measureReal_nonneg, ?_⟩
    calc (Ps n).real {x} ≤ (Ps n).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hK.tendsto_subseq hu
  have hcoord : ∀ x, Tendsto (fun j => u (φ j) x) atTop (𝓝 (a x)) :=
    fun x => tendsto_pi_nhds.1 hlim x
  have h0 : ∀ x, 0 ≤ a x := fun x => (ha x (Set.mem_univ x)).1
  have h1 : ∑ x, a x = 1 := by
    have : Tendsto (fun j => ∑ x, u (φ j) x) atTop (𝓝 (∑ x, a x)) :=
      tendsto_finsetSum _ (fun x _ => hcoord x)
    have hc : (fun j => ∑ x, u (φ j) x) = fun _ => (1:ℝ) := by
      funext j
      haveI := hPs (φ j)
      exact sum_real_one _
    rw [hc] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  obtain ⟨M, hM, hMx⟩ := exists_meas a h0 h1
  exact ⟨M, φ, hM, hφ, fun x => by rw [hMx]; exact hcoord x⟩

end IPFPc

namespace IPFPc

open Real Filter Topology IDivGeom.IPFP DcadKL

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

lemma term_cont (r : ℝ) : Continuous (fun p : ℝ => p * Real.log (p / r)) := by
  by_cases hr : r = 0
  · have e : (fun p : ℝ => p * Real.log (p / r)) = fun _ => 0 := by
      funext p
      simp [hr]
    rw [e]
    exact continuous_const
  · have e : (fun p : ℝ => p * Real.log (p / r)) = fun p => p * Real.log p - p * Real.log r := by
      funext p
      by_cases hp : p = 0
      · simp [hp]
      · rw [Real.log_div hp hr]
        ring
    rw [e]
    exact Real.continuous_mul_log.sub (continuous_id.mul continuous_const)

lemma kl_tendsto_fix (R : Measure X) [IsProbabilityMeasure R] (Ps : ℕ → Measure X)
    (hPs : ∀ n, IsProbabilityMeasure (Ps n)) (hac : ∀ n, Ps n ≪ R) (M : Measure X)
    [IsProbabilityMeasure M] (hMR : M ≪ R)
    (hlim : ∀ x, Tendsto (fun n => (Ps n).real {x}) atTop (𝓝 (M.real {x}))) :
    Tendsto (fun n => (klDiv (Ps n) R).toReal) atTop (𝓝 (klDiv M R).toReal) := by
  have e : (fun n => (klDiv (Ps n) R).toReal) = fun n =>
      ∑ x, (Ps n).real {x} * Real.log ((Ps n).real {x} / R.real {x}) := by
    funext n
    haveI := hPs n
    exact (kl_toReal _ _ (hac n)).2
  rw [e, (kl_toReal M R hMR).2]
  exact tendsto_finsetSum _ (fun x _ => ((term_cont (R.real {x})).tendsto _).comp (hlim x))

lemma kl_to_zero (Qs : ℕ → Measure X) (hQs : ∀ n, IsProbabilityMeasure (Qs n))
    (M : Measure X) [IsProbabilityMeasure M] (φ : ℕ → ℕ)
    (hlim : ∀ x, Tendsto (fun j => (Qs (φ j)).real {x}) atTop (𝓝 (M.real {x}))) :
    Tendsto (fun j => klDiv M (Qs (φ j))) atTop (𝓝 0) := by
  have hev : ∀ᶠ j in atTop, ∀ x, M.real {x} ≠ 0 → (Qs (φ j)).real {x} ≠ 0 := by
    rw [eventually_all]
    intro x
    by_cases hx : M.real {x} = 0
    · exact Eventually.of_forall (fun j h => absurd hx h)
    · have hpos : 0 < M.real {x} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hx)
      filter_upwards [(hlim x).eventually (lt_mem_nhds hpos)] with j hj _ using hj.ne'
  have hreal : Tendsto (fun j => ∑ x, M.real {x} * Real.log (M.real {x} / (Qs (φ j)).real {x}))
      atTop (𝓝 0) := by
    have h0 : (0:ℝ) = ∑ x, M.real {x} * Real.log (M.real {x} / M.real {x}) := by
      symm
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : M.real {x} = 0 <;> simp [hx]
    rw [h0]
    refine tendsto_finsetSum _ (fun x _ => ?_)
    by_cases hx : M.real {x} = 0
    · simp only [hx, zero_mul]
      exact tendsto_const_nhds
    · refine Tendsto.const_mul _ ?_
      exact ((Real.continuousAt_log (div_ne_zero hx hx)).tendsto).comp
        (tendsto_const_nhds.div (hlim x) hx)
  rw [← ENNReal.ofReal_zero]
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [hev] with j hj
  haveI := hQs (φ j)
  have hac : M ≪ Qs (φ j) := (ac_iff _ _).2 (fun x hx => by
    by_contra h
    exact hj x h hx)
  obtain ⟨hf, hv⟩ := kl_toReal M (Qs (φ j)) hac
  rw [← hv, ENNReal.ofReal_toReal hf]

lemma term_pw (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    (Real.sqrt p - Real.sqrt q) ^ 2 + (p - q) ≤ p * Real.log (p / q) := by
  by_cases hp0 : p = 0
  · subst hp0
    simp [Real.sq_sqrt hq]
  have hq0 : q ≠ 0 := fun h => hp0 (hpq h)
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  set a := Real.sqrt p with ha_def
  set b := Real.sqrt q with hb_def
  have ha : 0 < a := Real.sqrt_pos.2 hpp
  have hb : 0 < b := Real.sqrt_pos.2 hqp
  have hpa : p = a ^ 2 := (Real.sq_sqrt hp).symm
  have hqb : q = b ^ 2 := (Real.sq_sqrt hq).symm
  have hlog : Real.log (p / q) = 2 * Real.log (a / b) := by
    rw [hpa, hqb, ← div_pow, Real.log_pow]
    norm_num
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
  rw [inv_div] at h1
  have h2 : a ^ 2 * (1 - b / a) = a ^ 2 - a * b := by
    field_simp
  rw [hlog]
  have h3 : a ^ 2 * (1 - b / a) ≤ a ^ 2 * Real.log (a / b) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
  rw [hpa, hqb]
  nlinarith

lemma pw (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q)
    (x : X) : (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x})) ^ 2 ≤ (klDiv P Q).toReal := by
  rw [(kl_toReal P Q h).2]
  have hsum : ∑ y, ((Real.sqrt (P.real {y}) - Real.sqrt (Q.real {y})) ^ 2 +
      (P.real {y} - Q.real {y})) ≤ ∑ y, P.real {y} * Real.log (P.real {y} / Q.real {y}) :=
    Finset.sum_le_sum fun y _ => term_pw _ _ measureReal_nonneg measureReal_nonneg
      ((ac_iff P Q).1 h y)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_real_one, sum_real_one, sub_self,
    add_zero] at hsum
  refine le_trans ?_ hsum
  exact Finset.single_le_sum (f := fun y => (Real.sqrt (P.real {y}) - Real.sqrt (Q.real {y})) ^ 2)
    (fun y _ => sq_nonneg _) (Finset.mem_univ x)

lemma diff_bound (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q)
    (x : X) : |P.real {x} - Q.real {x}| ≤ 2 * Real.sqrt (klDiv P Q).toReal := by
  have hP1 : P.real {x} ≤ 1 := by
    calc P.real {x} ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hQ1 : Q.real {x} ≤ 1 := by
    calc Q.real {x} ≤ Q.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  set a := Real.sqrt (P.real {x})
  set b := Real.sqrt (Q.real {x})
  have ha1 : a ≤ 1 := Real.sqrt_le_one.2 hP1
  have hb1 : b ≤ 1 := Real.sqrt_le_one.2 hQ1
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have habs : |a - b| ≤ Real.sqrt (klDiv P Q).toReal := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (pw P Q h x)
  have e : P.real {x} - Q.real {x} = (a - b) * (a + b) := by
    have h1 : a ^ 2 = P.real {x} := Real.sq_sqrt measureReal_nonneg
    have h2 : b ^ 2 = Q.real {x} := Real.sq_sqrt measureReal_nonneg
    rw [← h1, ← h2]
    ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg ha0 hb0)]
  have hs : 0 ≤ Real.sqrt (klDiv P Q).toReal := Real.sqrt_nonneg _
  calc |a - b| * (a + b) ≤ Real.sqrt (klDiv P Q).toReal * (a + b) :=
        mul_le_mul_of_nonneg_right habs (add_nonneg ha0 hb0)
    _ ≤ Real.sqrt (klDiv P Q).toReal * 2 := mul_le_mul_of_nonneg_left (by linarith) hs
    _ = 2 * Real.sqrt (klDiv P Q).toReal := by ring

lemma tele (f : ℕ → ℝ) (n d : ℕ) :
    |f (n + d) - f n| ≤ ∑ l ∈ Finset.range d, |f (n + l + 1) - f (n + l)| := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    calc |f (n + (d + 1)) - f n| = |(f (n + d + 1) - f (n + d)) + (f (n + d) - f n)| := by
          rw [← add_assoc]
          ring_nf
      _ ≤ |f (n + d + 1) - f (n + d)| + |f (n + d) - f n| := abs_add_le _ _
      _ ≤ _ := by linarith

lemma clu (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X)) (hlin : ∀ i, IsLinearPD (ℰ i))
    (R : Measure X) (Qs : ℕ → Measure X) (hQs : IsCyclicIProjSeq hk ℰ R Qs)
    (hdiff : ∀ x, Tendsto (fun n => (Qs (n + 1)).real {x} - (Qs n).real {x}) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (M : Measure X) [IsProbabilityMeasure M]
    (hlim : ∀ x, Tendsto (fun j => (Qs (φ j)).real {x}) atTop (𝓝 (M.real {x}))) :
    M ∈ ⋂ i, ℰ i := by
  refine Set.mem_iInter.2 fun i => ?_
  set m : ℕ → ℕ := fun j => k * (φ j / k + 1) + i.val with hm_def
  have hd : ∀ j, ∃ d, d ≤ 2 * k ∧ m j + 1 = φ j + d := by
    intro j
    have h1 := Nat.div_add_mod (φ j) k
    have h2 := Nat.mod_lt (φ j) hk
    have h3 := i.isLt
    obtain ⟨A, hA⟩ : ∃ A, A = k * (φ j / k) := ⟨_, rfl⟩
    have hmj : m j = A + k + i.val := by
      simp only [hm_def, hA, mul_add, mul_one]
    rw [← hA] at h1
    exact ⟨m j + 1 - φ j, by omega, by omega⟩
  have hmod : ∀ j, cyc k (m j) hk = i := by
    intro j
    apply Fin.ext
    simp only [cyc, hm_def]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hmem : ∀ j, Qs (m j + 1) ∈ ℰ i := fun j => by
    rw [← hmod j]
    exact (hQs.2 (m j)).1
  have hD : ∀ x, Tendsto (fun n => ∑ l ∈ Finset.range (2 * k),
      |(Qs (n + l + 1)).real {x} - (Qs (n + l)).real {x}|) atTop (𝓝 0) := by
    intro x
    have : (0:ℝ) = ∑ l ∈ Finset.range (2 * k), (0:ℝ) := by simp
    rw [this]
    refine tendsto_finsetSum _ (fun l _ => ?_)
    have h := ((hdiff x).abs).comp (tendsto_add_atTop_nat l)
    simpa [Function.comp_def] using h
  have hclose : ∀ x j, |(Qs (m j + 1)).real {x} - (Qs (φ j)).real {x}| ≤
      ∑ l ∈ Finset.range (2 * k), |(Qs (φ j + l + 1)).real {x} - (Qs (φ j + l)).real {x}| := by
    intro x j
    obtain ⟨d, hd2, hdj⟩ := hd j
    rw [hdj]
    refine (tele (fun n => (Qs n).real {x}) (φ j) d).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd2)
      (fun _ _ _ => abs_nonneg _)
  refine closedL (hlin i) (fun j x => (Qs (m j + 1)).real {x}) (fun j => ⟨_, hmem j, fun x => rfl⟩)
    (fun x => M.real {x}) ?_ M (fun x => rfl)
  rw [tendsto_pi_nhds]
  intro x
  have h0 : Tendsto (fun j => (Qs (m j + 1)).real {x} - (Qs (φ j)).real {x}) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs]; exact hclose x j) ((hD x).comp hφ)
  have := (hlim x).add h0
  simpa using this

lemma exists_iproj (L : Set (Measure X)) (hL : IsLinearPD L) (R : Measure X)
    [IsProbabilityMeasure R] (hR : ∃ P ∈ L, P ≪ R) : ∃ Q, IsIProjection R L Q := by
  set S : Set ℝ := (fun P => (klDiv P R).toReal) '' {P | P ∈ L ∧ P ≪ R} with hS_def
  have hSne : S.Nonempty := by
    obtain ⟨P, hP, hPR⟩ := hR
    exact ⟨_, ⟨P, ⟨hP, hPR⟩, rfl⟩⟩
  have hSbdd : BddBelow S := ⟨0, by
    rintro _ ⟨P, _, rfl⟩
    exact ENNReal.toReal_nonneg⟩
  obtain ⟨vs, _, hvs_lim, hvs_mem⟩ := exists_seq_tendsto_sInf hSne hSbdd
  have hvs' : ∀ n, ∃ P, (P ∈ L ∧ P ≪ R) ∧ (klDiv P R).toReal = vs n := fun n => hvs_mem n
  choose Ps hPs hPsv using hvs'
  have hprob : ∀ n, IsProbabilityMeasure (Ps n) := fun n => hL.1 _ (hPs n).1
  obtain ⟨M, φ, hM, hφ, hlim⟩ := bw Ps hprob
  haveI := hM
  have hML : M ∈ L := closedL hL (fun j x => (Ps (φ j)).real {x})
    (fun j => ⟨_, (hPs (φ j)).1, fun x => rfl⟩) (fun x => M.real {x}) (tendsto_pi_nhds.2 hlim)
    M (fun x => rfl)
  have hMR : M ≪ R := (ac_iff M R).2 fun x hx => by
    have h0 : ∀ j, (Ps (φ j)).real {x} = 0 := fun j => (ac_iff _ _).1 (hPs (φ j)).2 x hx
    have hc : Tendsto (fun j => (Ps (φ j)).real {x}) atTop (𝓝 0) := by
      simp only [h0]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hlim x) hc
  have hcont := kl_tendsto_fix R (fun j => Ps (φ j)) (fun j => hprob _) (fun j => (hPs (φ j)).2)
    M hMR hlim
  have hval : (klDiv M R).toReal = sInf S := by
    have h2 : Tendsto (fun j => (klDiv (Ps (φ j)) R).toReal) atTop (𝓝 (sInf S)) := by
      have := hvs_lim.comp hφ.tendsto_atTop
      refine this.congr (fun j => ?_)
      simp [hPsv]
    exact tendsto_nhds_unique hcont h2
  have hMfin := (kl_toReal M R hMR).1
  refine ⟨M, hML, hMfin, fun P hP => ?_⟩
  by_cases hPR : P ≪ R
  · haveI := hL.1 P hP
    have hPfin := (kl_toReal P R hPR).1
    rw [← ENNReal.toReal_le_toReal hMfin hPfin, hval]
    exact csInf_le hSbdd ⟨P, ⟨hP, hPR⟩, rfl⟩
  · rw [klDiv_of_not_ac hPR]
    exact le_top

lemma exist_seq (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (R : Measure X) [IsProbabilityMeasure R] (P₀ : Measure X)
    [IsProbabilityMeasure P₀] (hP₀i : ∀ i, P₀ ∈ ℰ i) (hP₀R : P₀ ≪ R) :
    ∃ Qs : ℕ → Measure X, IsCyclicIProjSeq hk ℰ R Qs := by
  classical
  obtain ⟨step, hstepdef⟩ : ∃ step : ℕ → Measure X → Measure X, ∀ n μ,
      (∃ Q, IsIProjection μ (ℰ (cyc k n hk)) Q) → IsIProjection μ (ℰ (cyc k n hk)) (step n μ) :=
    ⟨fun n μ => if h : ∃ Q, IsIProjection μ (ℰ (cyc k n hk)) Q then h.choose else μ,
      fun n μ h => by
        dsimp only
        rw [dif_pos h]
        exact h.choose_spec⟩
  obtain ⟨Qs, hQ0, hQs⟩ : ∃ Qs : ℕ → Measure X, Qs 0 = R ∧ ∀ n, Qs (n + 1) = step n (Qs n) :=
    ⟨fun n => Nat.rec R (fun n μ => step n μ) n, rfl, fun n => rfl⟩
  have hstep : ∀ n, IsProbabilityMeasure (Qs n) → P₀ ≪ Qs n →
      IsIProjection (Qs n) (ℰ (cyc k n hk)) (Qs (n + 1)) := by
    intro n hp hac
    haveI := hp
    have hex : ∃ Q, IsIProjection (Qs n) (ℰ (cyc k n hk)) Q :=
      exists_iproj _ (hlin _) (Qs n) ⟨P₀, hP₀i _, hac⟩
    rw [hQs]
    exact hstepdef n (Qs n) hex
  have inv : ∀ n, IsProbabilityMeasure (Qs n) ∧ P₀ ≪ Qs n := by
    intro n
    induction n with
    | zero => exact ⟨by rw [hQ0]; infer_instance, by rw [hQ0]; exact hP₀R⟩
    | succ n ih =>
      obtain ⟨hp, hac⟩ := ih
      haveI := hp
      have hst := hstep n hp hac
      refine ⟨(hlin _).1 _ hst.1, ?_⟩
      haveI := (hlin _).1 _ hst.1
      have hpy := pyth _ (hlin _) (Qs n) (Qs (n + 1)) hst P₀ (hP₀i _)
      have hfin := (kl_toReal P₀ (Qs n) hac).1
      by_contra hna
      rw [klDiv_of_not_ac hna, top_add] at hpy
      exact hfin hpy
  exact ⟨Qs, hQ0, fun n => hstep n (inv n).1 (inv n).2⟩

lemma conv (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X)) (hlin : ∀ i, IsLinearPD (ℰ i))
    (R : Measure X) [IsProbabilityMeasure R] (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (hP₀ : P₀ ∈ ⋂ i, ℰ i) (hP₀R : P₀ ≪ R) (Qs : ℕ → Measure X)
    (hQs : IsCyclicIProjSeq hk ℰ R Qs) :
    ∃ Q, IsIProjection R (⋂ i, ℰ i) Q ∧
      ∀ x : X, Tendsto (fun n => (Qs n).real {x}) atTop (𝓝 (Q.real {x})) := by
  have hprob : ∀ m, IsProbabilityMeasure (Qs m) := by
    intro m
    cases m with
    | zero => rw [hQs.1]; infer_instance
    | succ m => exact (hlin _).1 _ (hQs.2 m).1
  have key : ∀ P ∈ ⋂ i, ℰ i, ∀ n : ℕ, klDiv P R = klDiv P (Qs n) +
      ∑ i ∈ Finset.range n, klDiv (Qs (i + 1)) (Qs i) := by
    intro P hP n
    have hPmem : ∀ i, P ∈ ℰ i := Set.mem_iInter.1 hP
    induction n with
    | zero => simp [hQs.1]
    | succ m ih =>
      haveI := hprob m
      rw [ih, pyth (ℰ (cyc k m hk)) (hlin _) (Qs m) (Qs (m + 1)) (hQs.2 m) P (hPmem _),
        Finset.sum_range_succ]
      ring
  set st : ℕ → ENNReal := fun i => klDiv (Qs (i + 1)) (Qs i) with hst_def
  set S := ∑' i, st i with hS_def
  have hSle : ∀ P ∈ ⋂ i, ℰ i, S ≤ klDiv P R := by
    intro P hP
    rw [hS_def, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    rw [key P hP n]
    exact le_add_self
  have hP₀fin : klDiv P₀ R ≠ ⊤ := (kl_toReal P₀ R hP₀R).1
  have hSfin : S ≠ ⊤ := ne_top_of_le_ne_top hP₀fin (hSle P₀ hP₀)
  have hst0 : Tendsto st atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hSfin
  have hstfin : ∀ n, st n ≠ ⊤ := fun n => ne_top_of_le_ne_top hSfin (ENNReal.le_tsum n)
  have hac : ∀ n, Qs (n + 1) ≪ Qs n := fun n => by
    by_contra h
    exact hstfin n (klDiv_of_not_ac h)
  have hdiff : ∀ x, Tendsto (fun n => (Qs (n + 1)).real {x} - (Qs n).real {x}) atTop (𝓝 0) := by
    intro x
    have hreal : Tendsto (fun n => (st n).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hst0
      rw [ENNReal.toReal_zero] at h
      exact h
    have hsq : Tendsto (fun n => 2 * Real.sqrt (st n).toReal) atTop (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).comp hreal).const_mul 2
    refine squeeze_zero_norm (fun n => ?_) hsq
    haveI := hprob n
    haveI := hprob (n + 1)
    rw [Real.norm_eq_abs]
    exact diff_bound _ _ (hac n) x
  have hclus : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ (M : Measure X),
      IsProbabilityMeasure M →
      (∀ x, Tendsto (fun j => (Qs (φ j)).real {x}) atTop (𝓝 (M.real {x}))) →
      IsIProjection R (⋂ i, ℰ i) M := by
    intro φ hφ M hMp hlim
    haveI := hMp
    have hME := clu k hk ℰ hlin R Qs hQs hdiff φ hφ M hlim
    have hKC := kl_to_zero Qs hprob M φ hlim
    have hle : klDiv M R ≤ S := by
      have h1 : Tendsto (fun j => klDiv M (Qs (φ j)) + S) atTop (𝓝 (0 + S)) :=
        hKC.add tendsto_const_nhds
      rw [zero_add] at h1
      refine ge_of_tendsto h1 (Eventually.of_forall fun j => ?_)
      rw [key M hME (φ j)]
      gcongr
      exact ENNReal.sum_le_tsum _
    exact ⟨hME, ne_top_of_le_ne_top hSfin hle, fun P hP => hle.trans (hSle P hP)⟩
  have huniq : ∀ M M', IsIProjection R (⋂ i, ℰ i) M → IsIProjection R (⋂ i, ℰ i) M' →
      M' = M := by
    intro M M' hM hM'
    have hlinE := linear_iInter hk ℰ hlin
    haveI := hlinE.1 M hM.1
    haveI := hlinE.1 M' hM'.1
    have hpy := pyth _ hlinE R M hM M' hM'.1
    have h1 : klDiv M' R ≤ klDiv M R := hM'.2.2 M hM.1
    rw [hpy] at h1
    have h0 : klDiv M' M = 0 :=
      le_antisymm (ENNReal.le_of_add_le_add_right hM.2.1 (by simpa using h1)) zero_le
    exact klDiv_eq_zero_iff.1 h0
  obtain ⟨Q, φ, hQp, hφ, hlim⟩ := bw Qs hprob
  have hQ := hclus φ hφ.tendsto_atTop Q hQp hlim
  refine ⟨Q, hQ, fun x => ?_⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨M', ψ, hM'p, hψ, hlim'⟩ := bw (fun j => Qs (ns j)) (fun j => hprob _)
  have hM' := hclus (fun j => ns (ψ j)) (hns.comp hψ.tendsto_atTop) M' hM'p hlim'
  have := huniq Q M' hQ hM'
  exact ⟨ψ, by rw [← this]; exact hlim' x⟩

end IPFPc

open MeasureTheory InformationTheory Filter Topology IDivGeom.IPFP in
theorem solution {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (k : ℕ) (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (hlin : ∀ i, IsLinearPD (ℰ i)) (hne : (⋂ i, ℰ i).Nonempty)
    (R : Measure X) [IsProbabilityMeasure R]
    (hR : ∃ P ∈ ⋂ i, ℰ i, P ≪ R) :
    (∃ Qs : ℕ → Measure X, IsCyclicIProjSeq hk ℰ R Qs) ∧
    ∀ Qs : ℕ → Measure X, IsCyclicIProjSeq hk ℰ R Qs →
      ∃ Q, IsIProjection R (⋂ i, ℰ i) Q ∧
        ∀ x : X, Tendsto (fun n => (Qs n).real {x}) atTop (𝓝 (Q.real {x})) := by
  obtain ⟨P₀, hP₀, hP₀R⟩ := hR
  have hP₀i : ∀ i, P₀ ∈ ℰ i := Set.mem_iInter.1 hP₀
  haveI : IsProbabilityMeasure P₀ := (hlin ⟨0, hk⟩).1 _ (hP₀i _)
  exact ⟨IPFPc.exist_seq k hk ℰ hlin R P₀ hP₀i hP₀R,
    fun Qs hQs => IPFPc.conv k hk ℰ hlin R P₀ hP₀ hP₀R Qs hQs⟩
