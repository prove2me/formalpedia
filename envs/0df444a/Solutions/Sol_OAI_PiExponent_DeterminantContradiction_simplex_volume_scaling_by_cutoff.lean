-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_scaling_by_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:44:03.769513+00:00
-- url     : https://prove2.me/submissions/ac15d1de-fe02-4d52-b0fd-0f065f54b243

import Definitions.Def_simplexRegion
import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

section

open MeasureTheory Set

namespace PiSimplex

noncomputable section

/-- the simplex `{x ≥ 0, ∑ x ≤ c}` -/
def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

lemma S_closed (n : ℕ) (c : ℝ) : IsClosed (S n c) := by
  unfold S
  refine IsClosed.inter ?_ ?_
  · have := isClosed_iInter fun i : Fin n =>
      isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply (A := fun _ : Fin n => ℝ) i)
    rw [Set.iInter_setOf] at this
    exact this
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := (S_closed n c).measurableSet

lemma S_neg (n : ℕ) {c : ℝ} (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le hc (Finset.sum_nonneg fun i _ => h i)

lemma slice (n : ℕ) (c t : ℝ) :
    {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} =
      if 0 ≤ t then S n (c - t) else ∅ := by
  ext y
  simp only [S, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  split_ifs with h
  · simp only [h, true_and, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · simp [h]

/-- the value of the volume -/
def F (n : ℕ) (c : ℝ) : ENNReal := if 0 ≤ c then ENNReal.ofReal (c ^ n / n.factorial) else 0

lemma integral_pow_sub (n : ℕ) (c : ℝ) :
    ∫ t in (0 : ℝ)..c, (c - t) ^ n / n.factorial = c ^ (n + 1) / (n + 1).factorial := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp only [sub_self, sub_zero, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma vol_succ (n : ℕ) (c : ℝ) :
    volume (S (n + 1) c) = ∫⁻ t, (if 0 ≤ t then volume (S n (c - t)) else 0) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  rw [← h.measure_preimage_equiv (S (n + 1) c)]
  rw [show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi (fun _ => volume) from rfl] at h
  rw [Measure.volume_eq_prod, Measure.prod_apply]
  · congr 1
    ext t
    have : Prod.mk t ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
        S (n + 1) c) = {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} := by
      ext y
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    rw [this, slice]
    split_ifs <;> simp
  · exact (MeasurableEquiv.measurable _) (S_meas _ _)

theorem vol_S (n : ℕ) (c : ℝ) : volume (S n c) = F n c := by
  induction n generalizing c with
  | zero =>
    unfold F
    split_ifs with hc
    · have : S 0 c = univ := by
        ext x; simp [S, hc]
      rw [this, volume_pi, Measure.pi_univ]; simp
    · rw [S_neg 0 (lt_of_not_ge hc)]; simp
  | succ n ih =>
    rw [vol_succ]
    simp_rw [ih]
    unfold F
    split_ifs with hc
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = (Icc 0 c).indicator (fun t => ENNReal.ofReal ((c - t) ^ n / n.factorial)) := by
        ext t
        simp only [indicator, mem_Icc, sub_nonneg]
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [this, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc, integral_pow_sub]
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have : 0 ≤ c - t := by linarith [ht.2]
        positivity
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = fun _ => 0 := by
        ext t
        split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)
      rw [this]; simp

theorem vol_S_of_nonneg (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rw [vol_S, F, if_pos hc]

end

end PiSimplex

end

section

open MeasureTheory Set PiSimplex Filter Topology

namespace PiL5

lemma lint (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ t in Set.Icc (0 : Real) r,
      ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real)) ∂MeasureTheory.volume) =
        ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hr, integral_pow_sub]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have : 0 ≤ r - t := by linarith [ht.2]
    positivity

theorem intpow (n : Nat) (r : Real) (hr : 0 ≤ r) :
    (∫⁻ t in Set.Icc (0 : Real) r,
      ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real)) ∂MeasureTheory.volume) =
        ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := lint n r hr

theorem powint (n : Nat) :
    ∫⁻ t in Set.Icc (0 : Real) 1,
      ENNReal.ofReal (((1 - t) ^ n) / (Nat.factorial n : Real))
      ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  simpa using lint n 1 zero_le_one

theorem dil (n : Nat) (c : Real) (hc : 0 ≤ c) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ c} =
    ENNReal.ofReal c ^ n *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  change volume (S n c) = _ * volume (S n 1)
  rw [vol_S_of_nonneg _ hc, vol_S_of_nonneg _ zero_le_one, ← ENNReal.ofReal_pow hc,
    ← ENNReal.ofReal_mul (by positivity), one_pow, mul_one_div]

/-- strict simplex -/
def S' (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i < c}

lemma S'_le (n : ℕ) (c : ℝ) : S' n c ⊆ S n c := fun x hx => ⟨hx.1, hx.2.le⟩

lemma vol_S' (n : ℕ) {c : ℝ} (hc : 0 < c) : volume (S' n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  apply le_antisymm
  · rw [← vol_S_of_nonneg n hc.le]; exact measure_mono (S'_le n c)
  · have hcont : Tendsto (fun c' : ℝ => ENNReal.ofReal (c' ^ n / n.factorial)) (𝓝[<] c)
        (𝓝 (ENNReal.ofReal (c ^ n / n.factorial))) :=
      (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun c' : ℝ => c' ^ n / n.factorial)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hcont ?_
    have : ∀ᶠ c' in 𝓝[<] c, 0 < c' := (eventually_gt_nhds hc).filter_mono nhdsWithin_le_nhds
    filter_upwards [this, self_mem_nhdsWithin] with c' h1 h2
    rw [← vol_S_of_nonneg n h1.le]
    exact measure_mono fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 h2⟩

lemma S'_empty (n : ℕ) {c : ℝ} (hc : c ≤ 0) : S' n c = ∅ := by
  ext x
  simp only [S', mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro h
  exact le_trans hc (Finset.sum_nonneg fun i _ => h i)

lemma region_meas (n : ℕ) (T : ℝ) :
    MeasurableSet (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) := by
  unfold OAI.PiExponent.DeterminantContradiction.simplexRegion
  refine MeasurableSet.inter (measurableSet_le measurable_const measurable_fst) (MeasurableSet.inter ?_ ?_)
  · have : MeasurableSet (⋂ i : Fin n, {z : ℝ × (Fin n → ℝ) | 0 ≤ z.2 i}) :=
      MeasurableSet.iInter fun i => measurableSet_le measurable_const
        ((measurable_pi_apply i).comp measurable_snd)
    rw [Set.iInter_setOf] at this
    exact this
  · exact measurableSet_lt (measurable_fst.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_snd)) measurable_const

lemma vol_region (n : ℕ) {T : ℝ} (hT : 0 < T) :
    volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) =
      ENNReal.ofReal (T ^ (n + 1) / (n + 1).factorial) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (region_meas n T)]
  have : ∀ t : ℝ, volume (Prod.mk t ⁻¹' OAI.PiExponent.DeterminantContradiction.simplexRegion n T) =
      (Ico 0 T).indicator (fun t => ENNReal.ofReal ((T - t) ^ n / n.factorial)) t := by
    intro t
    have hs : Prod.mk t ⁻¹' OAI.PiExponent.DeterminantContradiction.simplexRegion n T =
        if 0 ≤ t then S' n (T - t) else ∅ := by
      ext y
      simp only [OAI.PiExponent.DeterminantContradiction.simplexRegion, mem_preimage, mem_setOf_eq, S']
      split_ifs with h
      · simp only [h, true_and, mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      · simp [h]
    rw [hs]
    by_cases h0 : 0 ≤ t
    · rw [if_pos h0]
      by_cases h1 : t < T
      · rw [vol_S' n (by linarith), indicator_of_mem (show t ∈ Ico 0 T from ⟨h0, h1⟩)]
      · rw [S'_empty n (by linarith), measure_empty,
          indicator_of_notMem (show t ∉ Ico 0 T from fun hm => h1 hm.2)]
    · rw [if_neg h0, measure_empty, indicator_of_notMem (show t ∉ Ico 0 T from fun hm => h0 hm.1)]
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Ico, Measure.restrict_congr_set Ico_ae_eq_Icc, lint n T hT.le]

theorem unit_vol (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) = ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [vol_region n one_pos, one_pow]

theorem scaling (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) = ENNReal.ofReal (T ^ (n + 1)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by
  rw [vol_region n hT, vol_region n one_pos, one_pow, ← ENNReal.ofReal_mul (by positivity), mul_one_div]

end PiL5

end


open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) = ENNReal.ofReal (T ^ (n + 1)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by
  apply PiL5.scaling <;> assumption
