-- Prove2me | solution 1 for MassEnergyEquivalence.sum_mass_le_invariantMass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:54:59.960005+00:00
-- url     : https://prove2.me/submissions/dfa69f61-ec8f-43a2-8fa4-29f966147c26

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace LU3MassHelpers

open MassEnergyEquivalence

lemma pair (c : ℝ) (hc : 0 < c) (u w : Vec3) (hu : ‖u‖ < c) (hw : ‖w‖ < c) :
    c ^ 2 ≤ lorentzFactor c u * lorentzFactor c w * (c ^ 2 - inner ℝ u w) ∧
    (lorentzFactor c u * lorentzFactor c w * (c ^ 2 - inner ℝ u w) = c ^ 2 → u = w) := by
  set x := ‖u‖ ^ 2
  set y := ‖w‖ ^ 2
  set z := inner ℝ u w
  have hc2 : 0 < c ^ 2 := by positivity
  have hx : x < c ^ 2 := by simp only [x]; exact pow_lt_pow_left₀ hu (norm_nonneg _) two_ne_zero
  have hy : y < c ^ 2 := by simp only [y]; exact pow_lt_pow_left₀ hw (norm_nonneg _) two_ne_zero
  have hz : |z| ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
  have huw : ‖u‖ * ‖w‖ < c ^ 2 := by
    have := mul_lt_mul'' hu hw (norm_nonneg _) (norm_nonneg _); nlinarith
  have hzc : 0 < c ^ 2 - z := by have := le_abs_self z; linarith
  have hd : ‖u - w‖ ^ 2 = x - 2 * z + y := by
    rw [@norm_sub_sq_real]
  have hd0 : 0 ≤ x - 2 * z + y := by rw [← hd]; positivity
  have hiden : (c ^ 2 - z) ^ 2 - (c ^ 2 - x) * (c ^ 2 - y)
      = (x - 2 * z + y) * (c ^ 2 - y) + (z - y) ^ 2 := by ring
  set a := Real.sqrt (1 - x / c ^ 2)
  set b := Real.sqrt (1 - y / c ^ 2)
  have ha2 : a ^ 2 = 1 - x / c ^ 2 := Real.sq_sqrt (by rw [sub_nonneg, div_le_one hc2]; linarith)
  have hb2 : b ^ 2 = 1 - y / c ^ 2 := Real.sq_sqrt (by rw [sub_nonneg, div_le_one hc2]; linarith)
  have ha : 0 < a := Real.sqrt_pos.2 (by rw [sub_pos, div_lt_one hc2]; linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by rw [sub_pos, div_lt_one hc2]; linarith)
  have hab : (c ^ 2 * a * b) ^ 2 = (c ^ 2 - x) * (c ^ 2 - y) := by
    have : (c ^ 2 * a * b) ^ 2 = c ^ 2 * c ^ 2 * a ^ 2 * b ^ 2 := by ring
    rw [this, ha2, hb2]; field_simp
  have hL : lorentzFactor c u * lorentzFactor c w * (c ^ 2 - z) = (c ^ 2 - z) / (a * b) := by
    simp only [lorentzFactor, a, b, x, y]; field_simp
  rw [hL]
  have hpos : 0 < c ^ 2 * a * b := by positivity
  have key : c ^ 2 * a * b ≤ c ^ 2 - z := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self hzc.le hlt
    nlinarith [sq_nonneg (z - y), mul_nonneg hd0 (le_of_lt (sub_pos.2 hy))]
  constructor
  · rw [le_div_iff₀ (by positivity)]; linarith
  · intro h
    rw [div_eq_iff (by positivity)] at h
    have h1 : (c ^ 2 - z) ^ 2 = (c ^ 2 * a * b) ^ 2 := by rw [h]; ring
    have h2 : (x - 2 * z + y) * (c ^ 2 - y) = 0 := by
      nlinarith [sq_nonneg (z - y), mul_nonneg hd0 (le_of_lt (sub_pos.2 hy))]
    have h3 : x - 2 * z + y = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact h
      · exfalso; linarith
    rw [← hd] at h3
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
    exact sub_eq_zero.1 (norm_eq_zero.1 this)

lemma same (c : ℝ) (hc : 0 < c) (u : Vec3) (hu : ‖u‖ < c) :
    lorentzFactor c u * lorentzFactor c u * (c ^ 2 - inner ℝ u u) = c ^ 2 := by
  rw [real_inner_self_eq_norm_sq]
  have hc2 : 0 < c ^ 2 := by positivity
  have hx : ‖u‖ ^ 2 < c ^ 2 := pow_lt_pow_left₀ hu (norm_nonneg _) two_ne_zero
  have ha2 : Real.sqrt (1 - ‖u‖ ^ 2 / c ^ 2) ^ 2 = 1 - ‖u‖ ^ 2 / c ^ 2 :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hc2]; linarith)
  have ha : 0 < Real.sqrt (1 - ‖u‖ ^ 2 / c ^ 2) :=
    Real.sqrt_pos.2 (by rw [sub_pos, div_lt_one hc2]; linarith)
  unfold lorentzFactor
  rw [show 1 / Real.sqrt (1 - ‖u‖ ^ 2 / c ^ 2) * (1 / Real.sqrt (1 - ‖u‖ ^ 2 / c ^ 2))
      * (c ^ 2 - ‖u‖ ^ 2) = (c ^ 2 - ‖u‖ ^ 2) / Real.sqrt (1 - ‖u‖ ^ 2 / c ^ 2) ^ 2 by
      field_simp, ha2]
  have : c ^ 2 - ‖u‖ ^ 2 ≠ 0 := by linarith
  field_simp

end LU3MassHelpers

open LU3MassHelpers in
theorem solution {ι : Type*} (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (v : ι → Vec3) (hc : 0 < c) (hm : ∀ i ∈ s, 0 ≤ m i) (hv : ∀ i ∈ s, ‖v i‖ < c) :
    ∑ i ∈ s, m i ≤ invariantMass s c m v ∧
      ((∀ i ∈ s, 0 < m i) →
        (invariantMass s c m v = ∑ i ∈ s, m i ↔ ∀ i ∈ s, ∀ j ∈ s, v i = v j)) := by
  set g : ι → ℝ := fun i => lorentzFactor c (v i)
  set w : ι → ℝ := fun i => g i * m i
  set F : ι → ι → ℝ := fun i j => w i * w j * (c ^ 2 - inner ℝ (v i) (v j))
  have hc2 : 0 < c ^ 2 := by positivity
  have hE : ∑ i ∈ s, relEnergy c (m i) (v i) = c ^ 2 * ∑ i ∈ s, w i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [relEnergy, w, g]; ring
  have hP : ‖∑ i ∈ s, relMomentum c (m i) (v i)‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [relMomentum, w, g, real_inner_smul_left, real_inner_smul_right]; ring
  have hQ : (∑ i ∈ s, relEnergy c (m i) (v i)) ^ 2
      - c ^ 2 * ‖∑ i ∈ s, relMomentum c (m i) (v i)‖ ^ 2
      = c ^ 2 * ∑ i ∈ s, ∑ j ∈ s, F i j := by
    have hww : (∑ i ∈ s, w i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, w i * w j := by
      rw [sq, Finset.sum_mul_sum]
    rw [hE, hP]
    rw [show (c ^ 2 * ∑ i ∈ s, w i) ^ 2 - c ^ 2 * ∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)
      = c ^ 2 * (c ^ 2 * (∑ i ∈ s, w i) ^ 2
          - ∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) by ring]
    congr 1
    rw [hww, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [F]; ring
  have hF : ∀ i ∈ s, ∀ j ∈ s, m i * m j * c ^ 2 ≤ F i j ∧
      (F i j = m i * m j * c ^ 2 → 0 < m i * m j → v i = v j) := by
    intro i hi j hj
    obtain ⟨p1, p2⟩ := pair c hc (v i) (v j) (hv i hi) (hv j hj)
    have hmm : 0 ≤ m i * m j := mul_nonneg (hm i hi) (hm j hj)
    have e : F i j = m i * m j *
        (lorentzFactor c (v i) * lorentzFactor c (v j) * (c ^ 2 - inner ℝ (v i) (v j))) := by
      simp only [F, w, g]; ring
    rw [e]
    refine ⟨mul_le_mul_of_nonneg_left p1 hmm, fun h hp => p2 ?_⟩
    exact mul_left_cancel₀ hp.ne' h
  have hsumsq : ∑ i ∈ s, ∑ j ∈ s, m i * m j * c ^ 2 = c ^ 2 * (∑ i ∈ s, m i) ^ 2 := by
    rw [sq (∑ i ∈ s, m i), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have hle : c ^ 2 * (∑ i ∈ s, m i) ^ 2 ≤ ∑ i ∈ s, ∑ j ∈ s, F i j := by
    rw [← hsumsq]
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => (hF i hi j hj).1
  have hS0 : 0 ≤ ∑ i ∈ s, m i := Finset.sum_nonneg hm
  have hIM : invariantMass s c m v = Real.sqrt (∑ i ∈ s, ∑ j ∈ s, F i j) / c := by
    unfold invariantMass
    rw [hQ, Real.sqrt_mul hc2.le, Real.sqrt_sq hc.le]
    field_simp
  have hQ0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, F i j := le_trans (by positivity) hle
  have hdiff : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ F i j - m i * m j * c ^ 2 :=
    fun i hi j hj => sub_nonneg.2 (hF i hi j hj).1
  refine ⟨?_, fun hpos => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hIM, le_div_iff₀ hc, mul_comm, Real.le_sqrt (by positivity) hQ0]
    nlinarith
  · rw [hIM, div_eq_iff hc.ne'] at h
    have h2 : ∑ i ∈ s, ∑ j ∈ s, F i j = c ^ 2 * (∑ i ∈ s, m i) ^ 2 := by
      have := Real.sq_sqrt hQ0; rw [h] at this; rw [← this]; ring
    have h3 : ∑ i ∈ s, ∑ j ∈ s, (F i j - m i * m j * c ^ 2) = 0 := by
      simp only [Finset.sum_sub_distrib]; rw [h2, hsumsq]; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
      Finset.sum_nonneg fun j hj => hdiff i hi j hj] at h3
    intro i hi j hj
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j hj => hdiff i hi j hj).1 (h3 i hi) j hj
    exact (hF i hi j hj).2 (by linarith) (mul_pos (hpos i hi) (hpos j hj))
  · have h2 : ∑ i ∈ s, ∑ j ∈ s, F i j = c ^ 2 * (∑ i ∈ s, m i) ^ 2 := by
      rw [← hsumsq]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      have e : F i j = m i * m j *
          (lorentzFactor c (v i) * lorentzFactor c (v j) * (c ^ 2 - inner ℝ (v i) (v j))) := by
        simp only [F, w, g]; ring
      rw [e, ← h i hi j hj, same c hc (v i) (hv i hi)]
    rw [hIM, h2, Real.sqrt_mul hc2.le, Real.sqrt_sq hc.le, Real.sqrt_sq hS0]
    field_simp
