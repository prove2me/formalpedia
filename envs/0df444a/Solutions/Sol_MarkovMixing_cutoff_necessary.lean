-- Prove2me | solution 1 for MarkovMixing.cutoff_necessary
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T20:16:32.919983+00:00
-- url     : https://prove2.me/submissions/09232a5f-b768-4afb-bc29-518792b2fcfd

import Definitions.Def_mm_cutoff
import Theorems.Thm_MarkovMixing_relaxation_lower
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace CutNec

/-- `t_mix(ε)` is antitone in `ε` *as long as the tighter level is achieved at
all*: `mixingTime` is an `sInf` over the naturals, so an empty target set
reports the junk value `0` and monotonicity of the sets alone is not enough. -/
lemma mixingTime_anti {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hne : {t : ℕ | distStationary P π t ≤ a}.Nonempty) :
    mixingTime P π b ≤ mixingTime P π a := by
  have hm : mixingTime P π a ∈ {t : ℕ | distStationary P π t ≤ a} := Nat.sInf_mem hne
  exact Nat.sInf_le (le_trans hm hab)

/-- If the chain never gets within `1/4` of stationarity then `t_mix` is the
junk value `0`; contrapositively a positive `t_mix` certifies the target set is
nonempty. -/
lemma quarter_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) (h : 0 < tMix P π) :
    {t : ℕ | distStationary P π t ≤ 1 / 4}.Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have h0 : tMix P π = 0 := by
    show sInf {t : ℕ | distStationary P π t ≤ 1 / 4} = 0
    rw [hcon]
    exact Nat.sInf_empty
  omega

end CutNec

open CutNec

theorem solution {V : ℕ → Type*} [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] [∀ n, Nonempty (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ)
    (hP : ∀ n, MarkovMixing.IsStochastic (P n))
    (hirr : ∀ n, MarkovMixing.Irreducible (P n))
    (hap : ∀ n, MarkovMixing.Aperiodic (P n))
    (hπ : ∀ n, MarkovMixing.IsStationary (P n) (π n))
    (hrev : ∀ n, MarkovMixing.DetailedBalance (P n) (π n))
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n, (MarkovMixing.tMix (P n) (π n) : ℝ) ≤
      C * MarkovMixing.relaxationTime (P n))
    (hgrow : Filter.Tendsto (fun n => MarkovMixing.tMix (P n) (π n))
      Filter.atTop Filter.atTop) :
    ¬MarkovMixing.HasCutoff P π := by
  classical
  intro hcut
  -- the test level: `log (1/(2ε)) = 4C`
  set ε : ℝ := Real.exp (-(4 * C)) / 2 with hεdef
  have hexp1 : Real.exp (-(4 * C)) < 1 := by
    have : Real.exp (-(4 * C)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have hε0 : 0 < ε := by
    rw [hεdef]; positivity
  have hεhalf : ε < 1 / 2 := by
    rw [hεdef]; linarith
  have hε1 : ε < 1 := by linarith
  have hlog : Real.log (1 / (2 * ε)) = 4 * C := by
    have h2 : 2 * ε = Real.exp (-(4 * C)) := by rw [hεdef]; ring
    rw [h2, one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
  -- the ratio is eventually at least `2`, or degenerate
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C)
  have hkey : ∀ n : ℕ, ((N : ℝ) + 1) ≤ (MarkovMixing.tMix (P n) (π n) : ℝ) →
      1 / 2 ≤ |(MarkovMixing.mixingTime (P n) (π n) ε : ℝ) /
        (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) - 1| := by
    intro n hn
    set R : ℝ := MarkovMixing.relaxationTime (P n) with hR
    have hb := hbound n
    have htrel : 2 < R := by
      have h1 : (2 : ℝ) * C < C * R := by linarith
      nlinarith [hC]
    -- lower bound on `t_mix(ε)` from Theorem 12.4
    have hA : 4 * C * (R - 1) ≤ (MarkovMixing.mixingTime (P n) (π n) ε : ℝ) := by
      have := MarkovMixing.relaxation_lower (P n) (hP n) (hirr n) (hap n) (π n)
        (hπ n) (hrev n) ε hε0 hε1
      rw [hlog] at this
      linarith [this]
    -- upper bound on `t_mix(1−ε)`
    have hB : (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) ≤ C * R := by
      have hpos : 0 < MarkovMixing.tMix (P n) (π n) := by
        have : (1 : ℝ) ≤ (MarkovMixing.tMix (P n) (π n) : ℝ) := by
          have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
        exact_mod_cast this
      have h1 : MarkovMixing.mixingTime (P n) (π n) (1 - ε)
          ≤ MarkovMixing.mixingTime (P n) (π n) (1 / 4) :=
        mixingTime_anti (P n) (π n) (by linarith) (quarter_nonempty (P n) (π n) hpos)
      have h2 : (MarkovMixing.mixingTime (P n) (π n) (1 / 4) : ℝ)
          = (MarkovMixing.tMix (P n) (π n) : ℝ) := rfl
      have h3 : (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ)
          ≤ (MarkovMixing.tMix (P n) (π n) : ℝ) := by
        rw [← h2]
        exact_mod_cast h1
      linarith
    by_cases hz : MarkovMixing.mixingTime (P n) (π n) (1 - ε) = 0
    · rw [hz]
      norm_num
    · have hBpos : (0 : ℝ) < (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) := by
        have : 0 < MarkovMixing.mixingTime (P n) (π n) (1 - ε) := Nat.pos_of_ne_zero hz
        exact_mod_cast this
      have hratio : 2 ≤ (MarkovMixing.mixingTime (P n) (π n) ε : ℝ) /
          (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) := by
        rw [le_div_iff₀ hBpos]
        nlinarith [hA, hB, hC, htrel]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤
        (MarkovMixing.mixingTime (P n) (π n) ε : ℝ) /
          (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) - 1)]
      linarith
  -- but the cutoff hypothesis forces the ratio to `1`
  have hten := hcut ε hε0 hε1
  have h1 : ∀ᶠ n in Filter.atTop,
      |(MarkovMixing.mixingTime (P n) (π n) ε : ℝ) /
        (MarkovMixing.mixingTime (P n) (π n) (1 - ε) : ℝ) - 1| < 1 / 2 := by
    have := Metric.tendsto_nhds.mp hten (1 / 2) (by norm_num)
    simpa [Real.dist_eq] using this
  have h2 : ∀ᶠ n in Filter.atTop, ((N : ℝ) + 1) ≤ (MarkovMixing.tMix (P n) (π n) : ℝ) := by
    have h3 : ∀ᶠ n in Filter.atTop, N + 1 ≤ MarkovMixing.tMix (P n) (π n) :=
      hgrow.eventually_ge_atTop (N + 1)
    filter_upwards [h3] with n hn
    exact_mod_cast hn
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  linarith [hkey n hn2, hn1]
