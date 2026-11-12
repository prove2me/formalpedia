-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.n_way_separator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:57.792376+00:00
-- url     : https://prove2.me/submissions/0075eea1-a7aa-4cfa-9964-2f71a3956753

import Theorems.Thm_MomentAmbiguitySecretary_Secretary_entire_product_coefficients
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_moment_sums
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_all_moments
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_coefficient_profile

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.NWay

lemma coeff_unique (d : ℕ → ℂ) (h : ∀ z : ℂ, HasSum (fun j : ℕ => d j * z ^ j) 0) : d = 0 := by
  have hb : BddAbove (Set.range fun n : ℕ => ‖(FormalMultilinearSeries.ofScalars ℂ d) n‖ *
      ((1 : ℝ≥0) : ℝ) ^ n) := by
    apply Filter.Tendsto.bddAbove_range (a := 0)
    have := (h 1).summable.tendsto_atTop_zero.norm
    simpa using this
  obtain ⟨C, hC⟩ := hb
  have hrad : ((1 : ℝ≥0) : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ d).radius :=
    FormalMultilinearSeries.le_radius_of_bound _ C (fun n => hC ⟨n, rfl⟩)
  have hp : HasFPowerSeriesOnBall (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ d) 0 1 := by
    refine ⟨by simpa using hrad, by simp, ?_⟩
    intro y _
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, Pi.zero_apply]
    simpa using h y
  have := HasFPowerSeriesAt.eq_zero ⟨1, hp⟩
  funext n
  have h2 := congrFun this n
  have := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := d) n).1 h2
  simpa using this



open MomentAmbiguitySecretary.Secretary

lemma pow_inj (B : ℕ) (hB : 2 ≤ B) {j k : ℕ} (h : (B : ℝ≥0) ^ j = (B : ℝ≥0) ^ k) : j = k := by
  have h1 : (1 : ℝ≥0) < B := by exact_mod_cast hB
  exact (pow_right_strictMono₀ h1).injective h

lemma atom (B N h k : ℕ) (hB : 2 ≤ B) :
    residueMeasure B N h {((B : ℝ≥0) ^ k)} =
      ENNReal.ofReal (if k % N = h then coefficient B N k / normalizer B N else 0) := by
  unfold residueMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    have : ((B : ℝ≥0) ^ k) ≠ (B : ℝ≥0) ^ j := fun e => hj (pow_inj B hB e).symm
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), this.symm]

lemma coef_pos (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (j : ℕ) : 0 < coefficient B N j := by
  have := (coefficient_profile B N hB hN j).1
  have hp : (0:ℝ) < (B : ℝ) ^ (-(exponent N j : ℤ)) := by
    have : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    positivity
  linarith

lemma meas_univ (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    residueMeasure B N h.val univ = 1 := by
  obtain ⟨hs, hr, h1, _⟩ := residue_moment_sums B N hB hN
  have hW : 0 < normalizer B N := by linarith
  have hsum := (hs 0 h).1
  have hq : HasSum (fun j : ℕ => if j % N = h.val then coefficient B N j / normalizer B N else 0)
      (1 : ℝ) := by
    have := hsum.div_const (normalizer B N)
    have e : residueSum B N h.val 0 / normalizer B N = 1 := by
      rw [hr h]; exact div_self hW.ne'
    rw [e] at this
    refine this.congr_fun ?_  
    intro j; simp [residueTerm]; split_ifs <;> simp
  unfold residueMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.dirac_apply_of_mem (mem_univ _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg _ hq.summable, hq.tsum_eq]
  · simp
  · intro j; split_ifs
    · exact div_nonneg (coef_pos B N hB hN j).le hW.le
    · exact le_rfl

lemma supp_meas (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    residueMeasure B N h.val (residueSupport B N h.val) = 1 := by
  have hcount : (residueSupport B N h.val).Countable := by
    have : residueSupport B N h.val ⊆ Set.range (fun j : ℕ => (B : ℝ≥0) ^ j) := by
      rintro x ⟨j, _, rfl⟩; exact ⟨j, rfl⟩
    exact (Set.countable_range _).mono this
  have hm := hcount.measurableSet
  have hc : residueMeasure B N h.val (residueSupport B N h.val)ᶜ = 0 := by
    unfold residueMeasure
    rw [Measure.sum_apply _ hm.compl]
    refine ENNReal.tsum_eq_zero.2 fun j => ?_
    by_cases hj : j % N = h.val
    · have : (B : ℝ≥0) ^ j ∈ residueSupport B N h.val := ⟨j, hj, rfl⟩
      simp [Measure.dirac_apply' _ hm.compl, this]
    · simp [hj]
  have := measure_add_measure_compl (μ := residueMeasure B N h.val) hm
  rw [hc, add_zero, meas_univ B N hB hN h] at this
  exact this

end MomentAmbiguitySecretary.Secretary.Dev.NWay

namespace MomentAmbiguitySecretary.Secretary

open Dev.NWay in
theorem chk_n_way_separator (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (∀ z : ℂ, HasSum (fun j : ℕ => (coefficient B N j : ℂ) * z ^ j)
      (entireProduct B N z)) ∧
    (∀ a : ℕ → ℂ,
      (∀ z : ℂ, HasSum (fun j : ℕ => a j * z ^ j) (entireProduct B N z)) →
      a = fun j => (coefficient B N j : ℂ)) ∧
    1 ≤ normalizer B N ∧ normalizer B N < 4 ∧
    (∀ h : Fin N, IsProbabilityMeasure (residueMeasure B N h.val) ∧
      residueMeasure B N h.val (residueSupport B N h.val) = 1 ∧
      (∀ j : ℕ, residueMeasure B N h.val {((B : ℝ≥0) ^ j)} =
        ENNReal.ofReal (if j % N = h.val then coefficient B N j / normalizer B N else 0)) ∧
      (∀ t : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t)
        (residueMeasure B N h.val))) ∧
    (∀ h h' : Fin N, h ≠ h' → Disjoint (residueSupport B N h.val)
      (residueSupport B N h'.val)) ∧
    (∀ (h h' : Fin N) (t : ℕ),
      (∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h.val) =
        ∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h'.val) ∧
    coefficientProfile B N := by
  have hE := (entire_product_coefficients B N hB hN).2.2.2.2.1
  obtain ⟨_, _, h1, h4⟩ := residue_moment_sums B N hB hN
  refine ⟨hE, ?_, h1, h4, ?_, ?_, ?_, coefficient_profile B N hB hN⟩
  · intro a ha
    have := coeff_unique (fun j => a j - (coefficient B N j : ℂ)) (by
      intro z
      have := (ha z).sub (hE z)
      simpa [sub_mul] using this)
    funext j
    have := congrFun this j
    simpa [sub_eq_zero] using this
  · intro h
    exact ⟨⟨meas_univ B N hB hN h⟩, supp_meas B N hB hN h, fun j => atom B N h.val j hB,
      fun t => (residue_all_moments B N hB hN h h t).1⟩
  · intro h h' hne
    rw [Set.disjoint_left]
    rintro x ⟨j, hj, rfl⟩ ⟨k, hk, hjk⟩
    have := pow_inj B hB hjk
    subst this
    exact hne (Fin.ext (hj.symm.trans hk))
  · intro h h' t
    exact (residue_all_moments B N hB hN h h' t).2.2

end MomentAmbiguitySecretary.Secretary
end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_n_way_separator := @MomentAmbiguitySecretary.Secretary.chk_n_way_separator
