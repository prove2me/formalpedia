-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.ratio_increases_to_e_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:27:21.413078+00:00
-- url     : https://prove2.me/submissions/c638634f-042c-45a0-9787-795e0535fc1d

import Mathlib
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio



namespace NonuniformCompetitive.Isosceles

open Filter Topology

lemma iso_log_lo {P : ℝ} (hP : 0 < P) : 2 * P / (2 * P + 1) ≤ P * Real.log (1 + P⁻¹) := by
  have h := Real.hasSum_log_one_add_inv hP
  have h0 := le_hasSum h 0 (fun j _ => by positivity)
  simp at h0
  rw [div_le_iff₀ (by positivity)]
  have : 2 * (2 * P + 1)⁻¹ * (2 * P + 1) = 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h0 (by positivity : (0:ℝ) ≤ P * (2 * P + 1))
  nlinarith

lemma iso_log_hi {P : ℝ} (hP : 0 < P) : P * Real.log (1 + P⁻¹) ≤ (2 * P + 1) / (2 * P + 2) := by
  have h := Real.hasSum_log_one_add_inv hP
  set y : ℝ := 1 / (2 * P + 1) with hy
  have hy0 : 0 ≤ y ^ 2 := by positivity
  have hy1 : y ^ 2 < 1 := by
    have : 0 < y := by positivity
    have : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
    nlinarith
  have hg := (hasSum_geometric_of_lt_one hy0 hy1).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ => (by
    have hk : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ k := k.cast_nonneg; linarith
    have hyk : 0 ≤ y ^ (2 * k + 1) := by positivity
    have : y ^ (2 * k + 1) = y * (y ^ 2) ^ k := by rw [← pow_mul, pow_succ]; ring
    show 2 * (1 / (2 * (k:ℝ) + 1)) * y ^ (2 * k + 1) ≤ 2 * y * (y ^ 2) ^ k
    rw [this] at hyk ⊢
    nlinarith)) h hg
  have hval : P * (2 * y * (1 - y ^ 2)⁻¹) = (2 * P + 1) / (2 * P + 2) := by
    have hP0 : P ≠ 0 := hP.ne'
    have hP1 : P + 1 ≠ 0 := by linarith
    have hP2 : 2 * P + 1 ≠ 0 := by linarith
    have h1y : 1 - y ^ 2 = 4 * P * (P + 1) / (2 * P + 1) ^ 2 := by rw [hy]; field_simp; ring
    rw [h1y, hy]; field_simp; ring
  rw [← hval]
  exact mul_le_mul_of_nonneg_left hle hP.le

/-- `L P = P log (1 + 1/P)` -/
noncomputable def isoL (P : ℝ) : ℝ := P * Real.log (1 + P⁻¹)

lemma iso_eT_eq {d : ℕ} (hd : 1 ≤ d) : eTwoDSubOne d = Real.exp (isoL (2 * (d:ℝ) - 1)) := by
  have hx : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold eTwoDSubOne isoL
  have h1 : (2 * (d:ℝ)) / (2 * d - 1) = 1 + (2 * (d:ℝ) - 1)⁻¹ := by
    have : (2 * (d:ℝ) - 1) ≠ 0 := by linarith
    field_simp; ring
  rw [h1]
  have hpos : 0 < 1 + (2 * (d:ℝ) - 1)⁻¹ := by
    have : 0 < (2 * (d:ℝ) - 1)⁻¹ := inv_pos.2 (by linarith)
    linarith
  rw [← Real.exp_log hpos, ← Real.exp_nat_mul, Real.exp_log hpos]
  congr 2
  have : 1 ≤ 2 * d := by omega
  push_cast [Nat.cast_sub this]
  ring

lemma iso_step {d : ℕ} (hd : 2 ≤ d) : isoscelesRatio d < isoscelesRatio (d + 1) := by
  have hx : (2:ℝ) ≤ d := by exact_mod_cast hd
  set x : ℝ := (d:ℝ) with hxdef
  unfold isoscelesRatio
  rw [iso_eT_eq (by omega), iso_eT_eq (by omega)]
  push_cast
  rw [← hxdef]
  have hP : 0 < 2 * x - 1 := by linarith
  have hP' : 0 < 2 * (x + 1) - 1 := by linarith
  have lo := iso_log_lo hP
  have hi' := iso_log_hi hP'
  have hi := iso_log_hi hP
  have lo' := iso_log_lo hP'
  set L := isoL (2 * x - 1) with hL
  set L' := isoL (2 * (x + 1) - 1) with hL'
  have hlo : (4 * x - 2) / (4 * x - 1) ≤ L := by
    rw [hL, isoL]; convert lo using 1; ring_nf
  have hhi' : L' ≤ (4 * x + 3) / (4 * x + 4) := by
    rw [hL', isoL]; convert hi' using 1; ring_nf
  have hhi : L ≤ (4 * x - 1) / (4 * x) := by
    rw [hL, isoL]; convert hi using 1; ring_nf
  have hL0 : 0 ≤ L := by
    rw [hL, isoL]; have : 0 ≤ 2 * (2 * x - 1) / (2 * (2 * x - 1) + 1) := by positivity
    linarith
  have hL'0 : 0 ≤ L' := by
    rw [hL', isoL]; have : 0 ≤ 2 * (2 * (x+1) - 1) / (2 * (2 * (x+1) - 1) + 1) := by positivity
    linarith
  clear_value L L'
  set D : ℝ := 4 * x ^ 2 + 3 * x - 1 with hD
  have hD21 : 21 ≤ D := by nlinarith
  -- δ
  have hdelta : L' - L ≤ 5 / (4 * D) := by
    have : (4 * x + 3) / (4 * x + 4) - (4 * x - 2) / (4 * x - 1) = 5 / (4 * D) := by
      have h1 : 4 * x - 1 ≠ 0 := by linarith
      have h2 : 4 * x + 4 ≠ 0 := by linarith
      have h3 : D ≠ 0 := by linarith
      field_simp; rw [hD]; ring
    linarith
  set E := Real.exp L with hE
  set E' := Real.exp L' with hE'
  have hE1 : 1 ≤ E := by rw [hE]; linarith [Real.add_one_le_exp L]
  have hE'1 : 1 ≤ E' := by rw [hE']; linarith [Real.add_one_le_exp L']
  have hEe : E < 2.7183 := by
    have h1 : L < 1 := by
      have : (4 * x - 1) / (4 * x) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have := Real.exp_lt_exp.2 h1
    have := Real.exp_one_lt_d9
    rw [hE]; linarith
  -- E' (1 - δ) ≤ E
  have hkey : E' * (4 * D - 5) ≤ 4 * D * E := by
    have h1 : E' = E * Real.exp (L' - L) := by
      rw [hE, hE', ← Real.exp_add]; ring_nf
    have h2 : Real.exp (L' - L) * (1 - (L' - L)) ≤ 1 := by
      have := Real.add_one_le_exp (-(L' - L))
      have h3 : Real.exp (L' - L) * Real.exp (-(L' - L)) = 1 := by
        rw [← Real.exp_add]; simp
      have : 0 < Real.exp (L' - L) := Real.exp_pos _
      nlinarith
    have h4 : 1 - 5 / (4 * D) ≤ 1 - (L' - L) := by linarith
    have h5 : (4 * D - 5) = 4 * D * (1 - 5 / (4 * D)) := by field_simp
    rw [h5, h1]
    have hexp : 0 < Real.exp (L' - L) := Real.exp_pos _
    have hE0 : 0 < E := by linarith
    have : Real.exp (L' - L) * (1 - 5 / (4 * D)) ≤ 1 := by nlinarith
    have hD0 : 0 < 4 * D := by linarith
    calc E * Real.exp (L' - L) * (4 * D * (1 - 5 / (4 * D)))
        = 4 * D * E * (Real.exp (L' - L) * (1 - 5 / (4 * D))) := by ring
      _ ≤ 4 * D * E * 1 := by
          apply mul_le_mul_of_nonneg_left this; positivity
      _ = 4 * D * E := by ring
  have hmain : E' * D < E * (D + 1) + 1 := by
    have h1 : E' * D * (4 * D - 5) ≤ 4 * D * E * D := by nlinarith
    have h2 : 4 * D * E * D < (E * (D + 1) + 1) * (4 * D - 5) := by nlinarith
    have h3 : 0 < 4 * D - 5 := by linarith
    nlinarith
  clear_value E E'
  have hd1 : 0 < E - 1 + 1 / (2 * x) := by
    have : 0 < 1 / (2 * x) := by positivity
    linarith
  have hd2 : 0 < E' - 1 + 1 / (2 * (x + 1)) := by
    have : 0 < 1 / (2 * (x + 1)) := by positivity
    linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  have hx0 : 0 < x := by linarith
  have : (E' + 1 / (4 * (x + 1))) * (E - 1 + 1 / (2 * x)) -
      (E + 1 / (4 * x)) * (E' - 1 + 1 / (2 * (x + 1)))
      = (E * (D + 1) + 1 - E' * D) / (4 * x * (x + 1)) := by
    have h1 : x ≠ 0 := by linarith
    have h2 : x + 1 ≠ 0 := by linarith
    rw [hD]; field_simp; ring
  have : 0 < (E * (D + 1) + 1 - E' * D) / (4 * x * (x + 1)) := by
    apply div_pos (by linarith); positivity
  linarith

lemma iso_step1 : isoscelesRatio 1 < isoscelesRatio 2 := by
  norm_num [isoscelesRatio, eTwoDSubOne]

theorem ratio_increases_core :
    StrictMono (fun n : ℕ => isoscelesRatio (n + 1)) ∧
      Filter.Tendsto isoscelesRatio Filter.atTop
        (nhds (Real.exp 1 / (Real.exp 1 - 1))) := by
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact iso_step1
    · exact iso_step (by omega)
  · have hm : Tendsto (fun d : ℕ => 2 * d - 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun a ha => by omega⟩
    have hE : Tendsto eTwoDSubOne atTop (𝓝 (Real.exp 1)) := by
      have := (Real.tendsto_one_add_div_pow_exp 1).comp hm
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with d hd
      simp only [Function.comp, eTwoDSubOne]
      have hx : (1:ℝ) ≤ d := by exact_mod_cast hd
      have : 1 ≤ 2 * d := by omega
      congr 1
      push_cast [Nat.cast_sub this]
      have : (2 * (d:ℝ) - 1) ≠ 0 := by linarith
      field_simp
      ring
    have h4 : Tendsto (fun d : ℕ => 1 / (4 * (d:ℝ))) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (1/4 : ℝ)
      refine this.congr (fun d => ?_)
      rw [div_div]
    have h2 : Tendsto (fun d : ℕ => 1 / (2 * (d:ℝ))) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ)
      refine this.congr (fun d => ?_)
      rw [div_div]
    have hne : Real.exp 1 - 1 + 0 ≠ 0 := by
      have := Real.exp_one_gt_d9; norm_num at *; linarith
    have := (hE.add h4).div ((hE.sub_const 1).add h2) hne
    simp only [add_zero] at this
    exact this

end NonuniformCompetitive.Isosceles

open NonuniformCompetitive.Isosceles


theorem solution :
    StrictMono (fun n : ℕ => isoscelesRatio (n + 1)) ∧
      Filter.Tendsto isoscelesRatio Filter.atTop
        (nhds (Real.exp 1 / (Real.exp 1 - 1))) := by
  exact ratio_increases_core
