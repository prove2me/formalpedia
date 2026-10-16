-- Prove2me | solution 1 for OAI.ShortEgyptian.divisor_moment_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:20:02.422684+00:00
-- url     : https://prove2.me/submissions/6b32563e-5731-4482-92ae-e860e8f3fda5

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorMoments.lean:L50-L208
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.divisor_moment_finite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Theorems.Thm_OAI_ShortEgyptian_divisor_harmonic_bound
import Theorems.Thm_OAI_ShortEgyptian_prefix_weight_bound
import Theorems.Thm_OAI_ShortEgyptian_prime_prefix_split
import Theorems.Thm_OAI_ShortEgyptian_prime_reciprocals_bound
import Theorems.Thm_OAI_ShortEgyptian_rankin_divisor_weight
import Theorems.Thm_OAI_ShortEgyptian_sum_le_divisor_cover
import Theorems.Thm_OAI_ShortEgyptian_truncated_pointwise_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem momentSeriesConst_nonneg (r : ℕ) : 0 ≤ momentSeriesConst r := by
  exact tsum_nonneg (fun _ => by positivity)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.SmoothBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_reciprocals_real (T : ℝ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (1:ℝ)/p ≤ primeRecipBound T := by
  have h2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (prime_reciprocals_bound ⌊T⌋₊ h2).trans
  have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊T⌋₊))
    (Nat.floor_le (by linarith : 0 ≤ T))
  have hh : 0 ≤ Real.log (⌊T⌋₊:ℝ) := Real.log_natCast_nonneg _
  have harg : 0 < 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 := by positivity
  have hlog' := Real.log_le_log harg (show 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 ≤ 1+Real.log T/Real.log 2 by gcongr)
  unfold primeRecipBound
  linarith

theorem shifted_prime_sum (T lam : ℝ) (hT : 2 ≤ T) (hlam : 0 ≤ lam) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-(1-lam)) ≤
      T^lam * primeRecipBound T := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, T^lam * ((1:ℝ)/p) := by
      apply sum_le_sum
      intro p hp
      have hh := Nat.mem_primesLE.mp hp
      have hp0 : 0 < (p:ℝ) := by exact_mod_cast hh.2.pos
      have hpT : (p:ℝ) ≤ T := le_trans (by exact_mod_cast hh.1) (Nat.floor_le (by linarith))
      calc
        _ = (p:ℝ)^lam * ((1:ℝ)/p) := by
          rw [one_div, ← Real.rpow_neg_one,← Real.rpow_add hp0]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le hpT hlam) (by positivity)
    _ = T^lam * ∑ p ∈ Nat.primesLE ⌊T⌋₊, (1:ℝ)/p := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_reciprocals_real T hT) (Real.rpow_nonneg (by linarith) _)

theorem small_prime_sum (T : ℝ) (hT : 0 ≤ T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-(1-(1/10:ℝ))) ≤ T^(1/8:ℝ)*smallSmoothConst := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-41/40:ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, T^(1/8:ℝ)*(p:ℝ)^(-41/40:ℝ) := by
      apply sum_le_sum
      intro p hp
      have hh := Nat.mem_primesLE.mp hp
      have hp0 : 0 < (p:ℝ) := by exact_mod_cast hh.2.pos
      have hpT : (p:ℝ) ≤ T := le_trans (by exact_mod_cast hh.1) (Nat.floor_le hT)
      calc
        _ = (p:ℝ)^(1/8:ℝ)*(p:ℝ)^(-41/40:ℝ) := by rw [← Real.rpow_add hp0]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le hpT (by norm_num)) (Real.rpow_nonneg hp0.le _)
    _ = T^(1/8:ℝ) * ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-41/40:ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (Real.rpow_nonneg hT _)

theorem factored_primesLE {n : ℕ} (hn : n ≠ 0) {T : ℝ}
    (hs : ∀ p ∈ n.primeFactorsList, (p:ℝ) ≤ T) :
    n ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) := by
  refine ⟨hn, ?_⟩
  intro p hp
  exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp), Nat.prime_of_mem_primeFactorsList hp⟩

theorem smooth_prefix_sum (r : ℕ) (v T lam : ℝ) (hT : 2 ≤ T)
    (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/2) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) ∧ Real.exp (v/5) ≤ d) :
    ∑ d ∈ s, (d.divisors.card:ℝ)^r/d ≤
      Real.exp (-lam*v/5 + momentSeriesConst r * (T^lam * primeRecipBound T)) := by
  have hh := rankin_divisor_weight r (Real.exp (v/5)) lam (Real.exp_pos _) hlam hlam' s (Nat.primesLE ⌊T⌋₊) hs
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  rw [Real.log_exp, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hsum := mul_le_mul_of_nonneg_left (shifted_prime_sum T lam hT hlam) (momentSeriesConst_nonneg r)
  linarith

theorem small_smooth_prefix_sum (v T : ℝ) (hT : 0 ≤ T) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) ∧ Real.exp (v/5) ≤ d) :
    ∑ d ∈ s, (1:ℝ)/d ≤
      Real.exp (-v/50 + momentSeriesConst 0 * (T^(1/8:ℝ) * smallSmoothConst)) := by
  have hh := rankin_divisor_weight 0 (Real.exp (v/5)) (1/10) (Real.exp_pos _) (by norm_num) (by norm_num)
    s (Nat.primesLE ⌊T⌋₊) hs
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [pow_zero, Real.log_exp, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hsum := mul_le_mul_of_nonneg_left (small_prime_sum T hT) (momentSeriesConst_nonneg 0)
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorMoments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem pointwise_moment_bound {n : ℕ} (hn : n ≠ 0) (r : ℕ) (v W z : ℝ)
    (hv : 0 < v) (hvW : v < W) (hz : 1 < z) (hW : Real.log n ≤ W) :
    (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ Real.exp (momentPoint r v W z) := by
  have hW0 : 0 < W := hv.trans hvW
  have hq0 : 0 < v/W := div_pos hv hW0
  have hq1 : v/W < 1 := (div_lt_one hW0).mpr hvW
  have hh := truncated_pointwise_bound hn (Real.exp v) W z (v/W) hz hq0 hq1 hW
  have halg : v/W*W-Real.log (Real.exp v)*Real.log (v/W) = momentB v W := by
    rw [Real.log_exp, Real.log_div hv.ne' hW0.ne']
    unfold momentB
    rw [Real.log_div hW0.ne' hv.ne']
    field_simp
    ring
  rw [halg] at hh
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hh r
  simpa [momentPoint,Real.exp_nat_mul] using hp

theorem momentB_nonneg (v W : ℝ) (hv : 0 < v) (hvW : v < W) : 0 ≤ momentB v W := by
  have hq : 1 ≤ W/v := (le_div_iff₀ hv).mpr (by linarith)
  have hh := Real.log_nonneg hq
  unfold momentB
  positivity

theorem divisor_moment_finite (r : ℕ) (N : ℕ) (Y v W z T L : ℝ)
    (hY : 4 ≤ Y) (hv : 0 < v) (hvW : v < W) (hz : 1 < z)
    (hYv : v/2 ≤ Real.log Y) (hL : 0 < L) (hLv : L ≤ v/20)
    (hT : 2 ≤ Real.log T) (hTpos : 0 < T)
    (hnW : ∀ n ∈ Ioc N (N+⌊Y⌋₊), Real.log n ≤ W)
    (hsmall : momentPoint r v W z -v/50 + momentSeriesConst 0*(T^(1/8:ℝ)*smallSmoothConst) ≤ 0)
    (hband : ∀ t : ℝ, 1 ≤ t → Real.log T/2 ≤ t → t ≤ L →
      0 ≤ Real.log (v/t)/(10*t) ∧ Real.log (v/t)/(10*t) ≤ 1/2 ∧ momentBandExp r v W t ≤ 0) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤
      2*Y*(Real.exp ((r:ℝ)*momentB v W/L + momentSeriesConst r*primeRecipBound (Real.sqrt Y)) +
        (⌊L⌋₊:ℝ)+1) := by
  classical
  let R := Real.sqrt Y
  let K := ⌊L⌋₊
  let D (i : ℕ) : Finset ℕ := if i=0 then Icc 1 ⌊R⌋₊ else
    if i=1 then smoothPrefixes R v T else
    if Real.log T/2 ≤ (i-1:ℕ) then smoothPrefixes R v (Real.exp (2*(i-1:ℕ))) else ∅
  let F (i d : ℕ) : ℝ := if i=0 then
    Real.exp ((r:ℝ)*momentB v W/L)*(d.divisors.card:ℝ)^r else
    if i=1 then Real.exp (momentPoint r v W z) else
    Real.exp ((r:ℝ)*momentB v W/(i-1:ℕ))*(d.divisors.card:ℝ)^r
  have hR2 : 2 ≤ R := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hY)
  have hRpos : 0 < R := by linarith
  have hRY : R ≤ Y := by
    have hh : R*R = Y := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hRlog : v/4 ≤ Real.log R := by
    have hh : Real.log R = Real.log Y/2 := Real.log_sqrt (by linarith)
    linarith
  have hB : 0 ≤ (r:ℝ)*momentB v W := mul_nonneg (Nat.cast_nonneg r) (momentB_nonneg v W hv hvW)
  have hF (i d : ℕ) : 0 ≤ F i d := by unfold F; split_ifs <;> positivity
  have hD (i d : ℕ) (hd : d ∈ D i) : 0 < d ∧ (d:ℝ) ≤ Y := by
    have hh : d ∈ Icc 1 ⌊R⌋₊ := by
      unfold D at hd
      split_ifs at hd with h0 h1 ht
      · exact hd
      · exact (mem_filter.mp hd).1
      · exact (mem_filter.mp hd).1
      · simp at hd
    have hh' := mem_Icc.mp hh
    exact ⟨by omega, (le_trans (by exact_mod_cast hh'.2) (Nat.floor_le hRpos.le)).trans hRY⟩
  have hcover : ∀ n ∈ Ioc N (N+⌊Y⌋₊), ∃ i ∈ range (K+2), ∃ d ∈ D i,
      d ∣ n ∧ (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ F i d := by
    intro n hn
    have hnpos : 0 < n := by have hh := (mem_Ioc.mp hn).1; omega
    have hn0 : n ≠ 0 := hnpos.ne'
    by_cases hnR : (n:ℝ) ≤ R
    · refine ⟨0, mem_range.mpr (by omega), n, ?_, dvd_rfl, ?_⟩
      · simp only [D, ite_eq_left rfl]
        exact mem_Icc.mpr ⟨hnpos, Nat.le_floor hnR⟩
      · have hcard : truncatedDivisorCount (Real.exp v) n ≤ n.divisors.card := card_le_card (filter_subset _ _)
        have hc : (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ (n.divisors.card:ℝ)^r := by
          exact_mod_cast Nat.pow_le_pow_left hcard r
        have hexp : 1 ≤ Real.exp ((r:ℝ)*momentB v W/L) := Real.one_le_exp (div_nonneg hB hL.le)
        simpa [F] using hc.trans (le_mul_of_one_le_left (by positivity) hexp)
    · obtain ⟨d,e,p,hde,hd,he,hp,hpe,hdR,hRdp,hds,her⟩ :=
        prime_prefix_split hn0 R (by linarith) (lt_of_not_ge hnR)
      have hdpos : 0 < (d:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hppos : 0 < (p:ℝ) := by exact_mod_cast hp.pos
      have hlp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hdbase : d ∈ Icc 1 ⌊R⌋₊ := mem_Icc.mpr ⟨Nat.pos_of_ne_zero hd, Nat.le_floor hdR⟩
      have hdn : d ∣ n := hde ▸ dvd_mul_right d e
      have hpref := prefix_weight_bound hde hd he hp r v W hv hvW (hnW n hn) her
      have hpref' : (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤
        (d.divisors.card:ℝ)^r * Real.exp ((r:ℝ)*momentB v W/Real.log p) := by
        simpa [momentB, mul_assoc] using hpref
      by_cases hpL : L ≤ Real.log p
      · refine ⟨0, mem_range.mpr (by omega), d, by simpa [D] using hdbase, hdn, ?_⟩
        have hecomp := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hB hL hpL)
        simpa [F,mul_comm] using hpref'.trans (mul_le_mul_of_nonneg_left hecomp (by positivity))
      · have hpL' : Real.log (p:ℝ) < L := lt_of_not_ge hpL
        have hlogd : v/5 ≤ Real.log d := by
          have hh := Real.log_lt_log hRpos hRdp
          rw [Real.log_mul hdpos.ne' hppos.ne'] at hh
          linarith
        have hdA : Real.exp (v/5) ≤ (d:ℝ) := by
          simpa [Real.exp_log hdpos] using Real.exp_le_exp.mpr hlogd
        by_cases hpT : (p:ℝ) ≤ T
        · have hdsmooth := factored_primesLE hd (T := T) (fun q hq => le_trans (by exact_mod_cast hds q hq) hpT)
          refine ⟨1, mem_range.mpr (by omega), d, ?_, hdn, ?_⟩
          · change d ∈ smoothPrefixes R v T
            exact mem_filter.mpr ⟨hdbase,hdsmooth,hdA⟩
          · simpa [F] using pointwise_moment_bound hn0 r v W z hv hvW hz (hnW n hn)
        · let t := ⌊Real.log (p:ℝ)⌋₊
          have hlogpT : Real.log T < Real.log (p:ℝ) := Real.log_lt_log hTpos (lt_of_not_ge hpT)
          have ht2 : 2 ≤ t := Nat.le_floor (by norm_num; linarith)
          have ht1 : 1 ≤ (t:ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
          have htlog : (t:ℝ) ≤ Real.log (p:ℝ) := Nat.floor_le hlp.le
          have hlogt : Real.log (p:ℝ) < (t:ℝ)+1 := Nat.lt_floor_add_one _
          have htT : Real.log T/2 ≤ (t:ℝ) := by linarith
          have htK : t ≤ K := Nat.le_floor (htlog.trans hpL'.le)
          have hpt : (p:ℝ) ≤ Real.exp (2*(t:ℝ)) := by
            rw [← Real.exp_log hppos]
            exact Real.exp_le_exp.mpr (by linarith)
          have hdsmooth := factored_primesLE hd (T := Real.exp (2*(t:ℝ)))
            (fun q hq => le_trans (by exact_mod_cast hds q hq) hpt)
          refine ⟨t+1, mem_range.mpr (by omega), d, ?_, hdn, ?_⟩
          · have ht0 : t+1 ≠ 0 := by omega
            have htne1 : t+1 ≠ 1 := by omega
            dsimp only [D]
            rw [ite_eq_right ht0,ite_eq_right htne1,Nat.add_sub_cancel,ite_eq_left htT]
            exact mem_filter.mpr ⟨hdbase,hdsmooth,hdA⟩
          · have hecomp := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hB (by linarith : 0 < (t:ℝ)) htlog)
            have ht0 : t+1 ≠ 0 := by omega
            have htne1 : t+1 ≠ 1 := by omega
            dsimp only [F]
            rw [ite_eq_right ht0,ite_eq_right htne1,Nat.add_sub_cancel]
            simpa [mul_comm] using hpref'.trans (mul_le_mul_of_nonneg_left hecomp (by positivity))
  have hsum := sum_le_divisor_cover (range (K+2)) D F N Y (by linarith)
    (fun n => (truncatedDivisorCount (Real.exp v) n:ℝ)^r)
    (fun i _ d _ => hF i d) (fun i _ d hd => hD i d hd) hcover
  let E := (r:ℝ)*momentB v W/L + momentSeriesConst r*primeRecipBound R
  have hmass : ∀ i ∈ range (K+2), (∑ d ∈ D i, F i d/d) ≤ if i=0 then Real.exp E else 1 := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      simp only [D,F,ite_eq_left rfl]
      have hh := divisor_harmonic_bound r R hR2
      calc
        _ = Real.exp ((r:ℝ)*momentB v W/L) * ∑ d ∈ Icc 1 ⌊R⌋₊, (d.divisors.card:ℝ)^r/d := by rw [mul_sum]; apply sum_congr rfl; intro d hd; ring
        _ ≤ Real.exp ((r:ℝ)*momentB v W/L) * Real.exp (momentSeriesConst r*primeRecipBound R) :=
          mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
        _ = _ := (Real.exp_add _ _).symm
    · simp only [ite_eq_right hi0]
      by_cases hi1 : i=1
      · subst i
        simp only [D,F,ite_false,one_ne_zero]
        have hh := small_smooth_prefix_sum v T hTpos.le (smoothPrefixes R v T) (fun d hd => (mem_filter.mp hd).2)
        calc
          _ = Real.exp (momentPoint r v W z) * ∑ d ∈ smoothPrefixes R v T, (1:ℝ)/d := by rw [mul_sum]; simp [div_eq_mul_inv]
          _ ≤ Real.exp (momentPoint r v W z) * Real.exp (-v/50 + momentSeriesConst 0*(T^(1/8:ℝ)*smallSmoothConst)) :=
            mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
          _ ≤ 1 := by rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
      · by_cases htT : Real.log T/2 ≤ (i-1:ℕ)
        · have ht1 : 1 ≤ (i-1:ℕ) := by omega
          have ht1R : 1 ≤ ((i-1:ℕ):ℝ) := by exact_mod_cast ht1
          have htle : ((i-1:ℕ):ℝ) ≤ L := by
            have hh : i-1 ≤ K := by have hh := mem_range.mp hi; omega
            exact le_trans (by exact_mod_cast hh) (Nat.floor_le hL.le)
          have ht := hband (i-1:ℕ) ht1R htT htle
          have hTe : 2 ≤ Real.exp (2*((i-1:ℕ):ℝ)) := by
            have hh := Real.add_one_le_exp (2*((i-1:ℕ):ℝ))
            linarith
          have hh := smooth_prefix_sum r v (Real.exp (2*((i-1:ℕ):ℝ)))
            (Real.log (v/(i-1:ℕ))/(10*(i-1:ℕ))) hTe ht.1 ht.2.1
            (smoothPrefixes R v (Real.exp (2*((i-1:ℕ):ℝ)))) (fun d hd => (mem_filter.mp hd).2)
          simp only [D,F,ite_eq_right hi0,ite_eq_right hi1,ite_eq_left htT]
          calc
            _ = Real.exp ((r:ℝ)*momentB v W/(i-1:ℕ)) *
              ∑ d ∈ smoothPrefixes R v (Real.exp (2*((i-1:ℕ):ℝ))), (d.divisors.card:ℝ)^r/d := by rw [mul_sum]; apply sum_congr rfl; intro d hd; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
            _ ≤ 1 := by rw [← Real.exp_add, Real.exp_le_one_iff]; have ht' := ht.2.2; unfold momentBandExp at ht'; linarith
        · simp [D,hi0,hi1,htT]
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ i ∈ range (K+2), if i=0 then Real.exp E else 1 := sum_le_sum hmass
    _ = Real.exp E + (K:ℝ)+1 := by rw [sum_range_succ']; simp; ring
    _ = _ := rfl

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.divisor_moment_finite := @_root_.OAI.ShortEgyptian.divisor_moment_finite
