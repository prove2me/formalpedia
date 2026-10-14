-- Prove2me | solution 1 for OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T19:01:30.321472+00:00
-- url     : https://prove2.me/submissions/f845c836-3506-4dd1-be7b-923ed4bc567e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_VelocityHemisphere
import Theorems.Thm_OAI_DirectionalTransience_ballistic_of_almost_sure_transience
import Theorems.Thm_OAI_DirectionalTransience_uniformElliptic_directional_zero_one

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace OAI.DirectionalTransience.VH
open OAI.DirectionalTransience

lemma measurable_pathProj {d : ℕ} :
    Measurable (fun (z : (n : ℕ) → State d) (n : ℕ) => (z n).2) := by
  fun_prop

instance isProbabilityMeasure_initialLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (initialLaw ν) := by
  unfold initialLaw environmentLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance isProbabilityMeasure_annealedLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (annealedLaw ν) := by
  unfold annealedLaw
  exact Measure.isProbabilityMeasure_map measurable_pathProj.aemeasurable

lemma measurableSet_velocityPaths {d : ℕ} (v : Vector d) :
    MeasurableSet (VelocityPaths v) := by
  unfold VelocityPaths
  apply measurableSet_tendsto
  intro n
  fun_prop

/-- Two almost-sure velocities coincide. -/
lemma velocity_unique {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] {v w : Vector d}
    (hv : annealedLaw ν (VelocityPaths v) = 1) (hw : annealedLaw ν (VelocityPaths w) = 1) :
    v = w := by
  have h1 : ∀ᵐ X ∂(annealedLaw ν), X ∈ VelocityPaths v := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_velocityPaths v)).mpr hv
  have h2 : ∀ᵐ X ∂(annealedLaw ν), X ∈ VelocityPaths w := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_velocityPaths w)).mpr hw
  obtain ⟨X, hXv, hXw⟩ := (h1.and h2).exists
  exact tendsto_nhds_unique hXv hXw

lemma continuous_dot_left {d : ℕ} (u : Vector d) : Continuous (fun y : Vector d => dot y u) := by
  unfold dot
  fun_prop

/-- Escape: a path with velocity `v` is transient in every direction `u` with `0 < dot v u`. -/
lemma velocityPaths_subset_transientPaths {d : ℕ} {v u : Vector d} (h : 0 < dot v u) :
    VelocityPaths v ⊆ TransientPaths u := by
  intro X hX
  have hlim : Tendsto (fun n : ℕ => dot (fun i => (X n i : ℝ) / (n : ℝ)) u) atTop
      (𝓝 (dot v u)) := ((continuous_dot_left u).tendsto v).comp hX
  have hprod : Tendsto (fun n : ℕ => (n : ℝ) * dot (fun i => (X n i : ℝ) / (n : ℝ)) u) atTop
      atTop := tendsto_natCast_atTop_atTop.atTop_mul_pos h hlim
  show Tendsto (fun n => dot (realPosition (X n)) u) atTop atTop
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold dot realPosition
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  field_simp

lemma dot_div_right {d : ℕ} (x ℓ : Vector d) (r : ℝ) :
    dot x (fun i => ℓ i / r) = dot x ℓ / r := by
  unfold dot
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

lemma transientPaths_div {d : ℕ} (ℓ : Vector d) {r : ℝ} (hr : 0 < r) :
    TransientPaths (fun i => ℓ i / r) = TransientPaths ℓ := by
  ext X
  simp only [TransientPaths, Set.mem_ofPred_eq, dot_div_right]
  exact tendsto_div_const_atTop_of_pos hr

lemma dot_self_pos {d : ℕ} {ℓ : Vector d} (hℓ : ℓ ≠ 0) : 0 < dot ℓ ℓ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hℓ
  unfold dot
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg (ℓ j)) ⟨i, Finset.mem_univ _, ?_⟩
  exact mul_self_pos.mpr hi

lemma ne_zero_of_dot_self_eq_one {d : ℕ} {u : Vector d} (hu : dot u u = 1) : u ≠ 0 := by
  rintro rfl
  simp [dot] at hu

end OAI.DirectionalTransience.VH

open OAI.DirectionalTransience OAI.DirectionalTransience.VH in
theorem solution
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  have hd2 : 2 ≤ d := by omega
  -- zero-one law upgrades positivity to almost-sure transience
  have hT : annealedLaw ν (TransientPaths ℓ) = 1 := by
    rcases uniformElliptic_directional_zero_one hd ν hue ℓ hℓ with h | h
    · rw [h] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  -- normalize ℓ
  set r : ℝ := Real.sqrt (dot ℓ ℓ) with hr_def
  have hll : 0 < dot ℓ ℓ := dot_self_pos hℓ
  have hr : 0 < r := Real.sqrt_pos.mpr hll
  set u : Vector d := fun i => ℓ i / r with hu_def
  have hu1 : dot u u = 1 := by
    have h1 : dot u u = dot u ℓ / r := dot_div_right u ℓ r
    have h2 : dot u ℓ = dot ℓ ℓ / r := by
      unfold dot
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [hu_def]
      ring
    rw [h1, h2, div_div, ← sq, Real.sq_sqrt hll.le, div_self hll.ne']
  have hTu : annealedLaw ν (TransientPaths u) = 1 := by
    rw [hu_def, transientPaths_div ℓ hr]; exact hT
  obtain ⟨v, hvu, hvV⟩ := ballistic_of_almost_sure_transience hd2 ν hue u hu1 hTu
  have hvℓ : 0 < dot v ℓ := by
    have : dot v u = dot v ℓ / r := dot_div_right v ℓ r
    rw [this] at hvu
    exact (div_pos_iff_of_pos_right hr).mp hvu
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [dot] at hvℓ
  have huniq : ∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v :=
    fun w hw => velocity_unique ν hw hvV
  -- key equivalence for unit directions
  have hkey : ∀ u' : Vector d, dot u' u' = 1 →
      (0 < annealedLaw ν (TransientPaths u') ↔ 0 < dot v u') := by
    intro u' hu'
    constructor
    · intro hp
      have h1 : annealedLaw ν (TransientPaths u') = 1 := by
        rcases uniformElliptic_directional_zero_one hd ν hue u'
            (ne_zero_of_dot_self_eq_one hu') with h | h
        · rw [h] at hp; exact absurd hp (lt_irrefl 0)
        · exact h
      obtain ⟨w, hwu, hwV⟩ := ballistic_of_almost_sure_transience hd2 ν hue u' hu' h1
      rw [← huniq w hwV]
      exact hwu
    · intro hp
      have hle : annealedLaw ν (VelocityPaths v) ≤ annealedLaw ν (TransientPaths u') :=
        measure_mono (velocityPaths_subset_transientPaths hp)
      rw [hvV] at hle
      exact lt_of_lt_of_le one_pos hle
  refine ⟨v, hv0, hvℓ, hvV, huniq, ?_, ?_, ?_⟩
  · ext u'
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu', h⟩
      exact ⟨hu', by rw [h]; exact one_pos⟩
    · rintro ⟨hu', h⟩
      refine ⟨hu', ?_⟩
      rcases uniformElliptic_directional_zero_one hd ν hue u'
          (ne_zero_of_dot_self_eq_one hu') with h' | h'
      · rw [h'] at h; exact absurd h (lt_irrefl 0)
      · exact h'
  · ext u'
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu', h⟩
      exact ⟨hu', (hkey u' hu').mp h⟩
    · rintro ⟨hu', h⟩
      exact ⟨hu', (hkey u' hu').mpr h⟩
  · intro u' hu' hle
    rcases uniformElliptic_directional_zero_one hd ν hue u'
        (ne_zero_of_dot_self_eq_one hu') with h | h
    · exact h
    · exfalso
      have : 0 < dot v u' := (hkey u' hu').mp (by rw [h]; exact one_pos)
      linarith
