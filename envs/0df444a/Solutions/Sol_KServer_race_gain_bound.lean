-- Prove2me | solution 1 for KServer.race_gain_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T19:44:20.727748+00:00
-- url     : https://prove2.me/submissions/997401fa-8c5b-41e3-9516-4ea8fe16886e

import Mathlib
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_gain
import Definitions.Def_KServer_discrete_martingale
import Theorems.Thm_KServer_martingale_abs_anticoncentration

set_option maxHeartbeats 3200000

namespace KServer

open Race

theorem race_gain_bound {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {cLo' : ℝ} (hεLo : ε ≤ cLo')
    (hLoL : ∀ (l : BL.Ω) (i : Fin BL.m), cLo' ≤ BL.size l i)
    (hLoR : ∀ (r : BR.Ω) (i : Fin BR.m), cLo' ≤ BR.size r i) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| := by
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  have hE0 : 0 ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (hRP0 ω) (abs_nonneg _)
  by_cases hκ0 : κ = 0
  · subst hκ0
    simp only [Nat.cast_zero, zero_mul]
    norm_num
    exact hE0
  · have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hκ0
    have hγpos : (0 : ℝ) < cB + ε := by linarith
    have hCpos : (0 : ℝ) < 8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
        + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2) := by
      have h1 : (0 : ℝ) < (κ : ℝ) * (cB + ε) ^ 2 := by
        have := pow_pos hγpos 2
        nlinarith
      nlinarith [sq_nonneg ((κ : ℝ) * (cB + ε) ^ 2), pow_pos hγpos 2]
    have hanti := martingale_abs_anticoncentration
      (RP A BL BR CC κ ε) κ (ghist A BL BR CC κ)
      (mgX A BL BR CC κ ε) (mgV A BL BR CC κ ε)
      (race_martingale A BL BR CC κ ε hε)
      (cB + ε) ((κ : ℝ) * (cB + ε) ^ 2) ((κ : ℝ) * cLo' ^ 2)
      hγpos.le
      (fun j _ ω => mgX_abs_le A BL BR CC κ ε hε hcB j ω)
      (fun j _ ω => mgV_nonneg A BL BR CC κ ε hε j ω)
      (fun ω => mgV_total_le A BL BR CC κ ε hε hcB ω)
      (fun ω => mgV_total_ge A BL BR CC κ ε hε hκL hκR hεLo hLoL hLoR ω)
      (by positivity) (by positivity)
      (RP_sum A BL BR CC κ ε hε)
    have hred := race_gain_reduce A BL BR CC κ ε hε
    have hm0 : 0 ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |mgSum (mgX A BL BR CC κ ε) κ ω| :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (hRP0 ω) (abs_nonneg _)
    have h2 : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |mgSum (mgX A BL BR CC κ ε) κ ω|) ^ 2
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε) ^ 2 := by
      have h2a := pow_le_pow_left₀ hm0 hred 2
      exact h2a
    have h3 : ((κ : ℝ) * cLo' ^ 2) ^ 3
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε) ^ 2
          * (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
            + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)) :=
      le_trans hanti (mul_le_mul_of_nonneg_right h2 hCpos.le)
    have h4 : ((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2))
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε) ^ 2 :=
      (div_le_iff₀ hCpos).mpr h3
    have hEκ : 0 ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|) + (κ : ℝ) * ε := by
      have : (0 : ℝ) ≤ (κ : ℝ) * ε := by positivity
      linarith
    have h5 : Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
        ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε := by
      refine le_trans (Real.sqrt_le_sqrt h4) (le_of_eq ?_)
      exact Real.sqrt_sq hEκ
    linarith

end KServer

open KServer Race in
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {cLo' : ℝ} (hεLo : ε ≤ cLo')
    (hLoL : ∀ (l : BL.Ω) (i : Fin BL.m), cLo' ≤ BL.size l i)
    (hLoR : ∀ (r : BR.Ω) (i : Fin BR.m), cLo' ≤ BR.size r i) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| :=
  KServer.race_gain_bound A BL BR CC κ ε hε hκL hκR hcB hεLo hLoL hLoR
