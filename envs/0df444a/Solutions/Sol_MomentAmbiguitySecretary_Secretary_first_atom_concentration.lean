-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.first_atom_concentration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:59.367695+00:00
-- url     : https://prove2.me/submissions/6908ccd7-b34a-4d55-a6ca-de69745d3f51

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_moment_sums
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_coefficient_profile

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.NWay



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

end MomentAmbiguitySecretary.Secretary.Dev.NWay

namespace MomentAmbiguitySecretary.Secretary

end MomentAmbiguitySecretary.Secretary
end

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.FirstAtom

open MomentAmbiguitySecretary.Secretary MomentAmbiguitySecretary.Secretary.Dev.NWay

lemma exp_small (N h : ℕ) (hN : 2 ≤ N) (hh : h < N) : exponent N h = 0 := by
  unfold exponent
  simp only
  by_cases h1 : h < N - 1
  · have : h / (N - 1) = 0 := Nat.div_eq_of_lt h1
    simp [this]
  · have e : h = N - 1 := by omega
    subst e
    have : (N - 1) / (N - 1) = 1 := Nat.div_self (by omega)
    simp [this]

lemma term_le (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (j : ℕ) :
    residueTerm B N 0 0 j ≤ if j % N = 0 then (((2:ℝ) ^ N) / B) ^ (j / N) else 0 := by
  unfold residueTerm
  by_cases hj : j % N = 0
  · simp only [hj, if_true, zero_mul, pow_zero, mul_one]
    obtain ⟨k, rfl⟩ : ∃ k, j = N * k := ⟨j / N, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hj)).symm⟩
    have hk : N * k / N = k := Nat.mul_div_cancel_left _ (by omega)
    rw [hk]
    obtain ⟨h1, h2, h3, _⟩ := coefficient_profile B N hB hN (N * k)
    have hBpos : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have : exponent N 0 = 0 := exp_small N 0 hN (by omega)
      simp only [mul_zero, this] at h2 ⊢
      simpa using h2
    · have he : (k : ℤ) ≤ exponent N (N * k) := by
        have : (N:ℤ) * k - exponent N (N * k) ≤ N - 1 := by exact_mod_cast h3
        have h4 : (1:ℤ) ≤ k := by exact_mod_cast hk0
        have h5 : (2:ℤ) ≤ N := by exact_mod_cast hN
        nlinarith
      have h6 : (B:ℝ) ^ (-(exponent N (N * k) : ℤ)) ≤ (B:ℝ) ^ (-(k:ℤ)) :=
        zpow_le_zpow_right₀ (by exact_mod_cast (by omega : 1 ≤ B)) (by omega)
      calc coefficient B N (N * k) ≤ _ := h2
        _ ≤ (2:ℝ) ^ (N * k) * (B:ℝ) ^ (-(k:ℤ)) := by gcongr
        _ = (((2:ℝ) ^ N) / B) ^ k := by
          rw [div_pow, pow_mul, zpow_neg, zpow_natCast, div_eq_mul_inv]
  · simp [hj]

lemma W_le (B N : ℕ) (hN : 2 ≤ N) (hB : 2 ^ N < B) :
    normalizer B N ≤ 1 / (1 - ((2:ℝ) ^ N) / B) := by
  have hB2 : 2 ≤ B := by
    have : 4 ≤ 2 ^ N := by calc 4 = 2 ^ 2 := by norm_num
                                 _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have hBpos : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set r : ℝ := ((2:ℝ) ^ N) / B with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hBpos]; exact_mod_cast hB
  set g : ℕ → ℝ := fun j => if j % N = 0 then r ^ (j / N) else 0 with hg
  have hgs : HasSum g (1 / (1 - r)) := by
    have h0 : HasSum (fun k : ℕ => r ^ k) (1 / (1 - r)) := by
      simpa [one_div] using hasSum_geometric_of_lt_one hr0 hr1
    have hinj : Function.Injective (fun k : ℕ => N * k) := fun a b h => by
      simpa [show N ≠ 0 by omega] using h
    have hsupp : Function.support g ⊆ Set.range (fun k : ℕ => N * k) := by
      intro j hj
      by_contra hn
      apply hj
      have : j % N ≠ 0 := fun h0 => hn ⟨j / N, by simpa using Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)⟩
      simp [hg, this]
    rw [← hinj.hasSum_iff (fun j hj => by
      by_contra hn; exact hj (by simpa using hsupp (show j ∈ Function.support g from hn)) )]
    convert h0 using 1
    funext k
    simp [hg, show N ≠ 0 by omega, Nat.mul_div_cancel_left _ (show 0 < N by omega)]
  have hs := ((residue_moment_sums B N hB2 hN).1 0 ⟨0, by omega⟩).1.summable
  have := Summable.tsum_le_tsum (fun j => term_le B N hB2 hN j) hs hgs.summable
  calc normalizer B N = ∑' j, residueTerm B N 0 0 j := rfl
    _ ≤ ∑' j, g j := this
    _ = _ := hgs.tsum_eq



lemma atom_val (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    (residueMeasure B N h.val {((B : ℝ≥0) ^ h.val)}).toReal =
      coefficient B N h.val / normalizer B N := by
  rw [atom B N h.val h.val hB, if_pos (Nat.mod_eq_of_lt h.isLt)]
  have hW : 0 < normalizer B N := by linarith [(residue_moment_sums B N hB hN).2.2.1]
  exact ENNReal.toReal_ofReal (div_nonneg (coef_pos B N hB hN _).le hW.le)

lemma bounds (B N : ℕ) (hN : 2 ≤ N) (hB : 2 ^ N < B) :
    1 - ((2:ℝ) ^ N) / B ≤ minimumFirstAtom B N ∧ minimumFirstAtom B N ≤ 1 := by
  have hB2 : 2 ≤ B := by
    have : 4 ≤ 2 ^ N := by calc 4 = 2 ^ 2 := by norm_num
                                 _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have hBpos : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hr1 : ((2:ℝ) ^ N) / B < 1 := by
    rw [div_lt_one hBpos]; exact_mod_cast hB
  have hW1 : 1 ≤ normalizer B N := (residue_moment_sums B N hB2 hN).2.2.1
  have hWup := W_le B N hN hB
  have hlow : ∀ h : Fin N, 1 - ((2:ℝ) ^ N) / B ≤ coefficient B N h.val / normalizer B N := by
    intro h
    have hc : 1 ≤ coefficient B N h.val := by
      have := (coefficient_profile B N hB2 hN h.val).1
      rwa [exp_small N h.val hN h.isLt, Int.natCast_zero, neg_zero, zpow_zero] at this
    have hpos : 0 < 1 - ((2:ℝ) ^ N) / B := by linarith
    have h1 : 1 - ((2:ℝ) ^ N) / B ≤ 1 / normalizer B N := by
      rw [le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hWup hpos.le
      rwa [mul_one_div_cancel hpos.ne'] at this
    calc _ ≤ 1 / normalizer B N := h1
      _ ≤ _ := by gcongr
  have hup : ∀ h : Fin N, coefficient B N h.val / normalizer B N ≤ 1 := by
    intro h
    haveI : IsProbabilityMeasure (residueMeasure B N h.val) := ⟨meas_univ B N hB2 hN h⟩
    rw [← atom_val B N hB2 hN h]
    have := ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := residueMeasure B N h.val) (s := {((B : ℝ≥0) ^ h.val)}))
    simpa using this
  have hN0 : 0 < N := by omega
  unfold minimumFirstAtom
  rw [dif_pos hN0]
  constructor
  · apply Finset.le_inf'
    intro h _
    rw [atom_val B N hB2 hN h]; exact hlow h
  · obtain ⟨h0⟩ : Nonempty (Fin N) := ⟨⟨0, hN0⟩⟩
    refine (Finset.inf'_le _ (Finset.mem_univ h0)).trans ?_
    rw [atom_val B N hB2 hN h0]; exact hup h0

end MomentAmbiguitySecretary.Secretary.Dev.FirstAtom

namespace MomentAmbiguitySecretary.Secretary

theorem chk_first_atom_concentration (N : ℕ) (hN : 2 ≤ N) :
    Tendsto (fun B : ℕ => minimumFirstAtom B N) atTop (𝓝 1) := by
  have hlim : Tendsto (fun B : ℕ => 1 - ((2:ℝ) ^ N) / (B : ℝ)) atTop (𝓝 1) := by
    have : Tendsto (fun B : ℕ => ((2:ℝ) ^ N) / (B : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (2 ^ N)] with B hB
    exact (Dev.FirstAtom.bounds B N hN hB).1
  · filter_upwards [eventually_gt_atTop (2 ^ N)] with B hB
    exact (Dev.FirstAtom.bounds B N hN hB).2

end MomentAmbiguitySecretary.Secretary
end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_first_atom_concentration := @MomentAmbiguitySecretary.Secretary.chk_first_atom_concentration
