-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:24:18.818732+00:00
-- url     : https://prove2.me/submissions/d9cf6ad2-f4ea-47d5-ad78-bfcbffddaa91

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling ErlangA.Diffusion
open MartingaleHT.InfiniteServer

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hcad : ∀ n : ℕ, 1 ≤ n → ∀ ω i, IsCadlag (fun t => X n ω t i))
    (hmeas : ∀ n : ℕ, 1 ≤ n → ∀ t, Measurable (fun ω => X n ω t))
    (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hlim : Tendsto a atTop atTop)
    (hSB : IsSBD P X) :
    UocInProb P (fun n ω t => (a n)⁻¹ • X n ω t) (fun _ => 0) := by
  intro t ht ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  set δr : ℝ := (min δ 1).toReal with hδr
  have hmin_ne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hδr_pos : 0 < δr := by
    rw [hδr]; exact ENNReal.toReal_pos (by simp [hδ.ne']) hmin_ne
  have hδr_le : ENNReal.ofReal δr ≤ δ := by
    rw [hδr, ENNReal.ofReal_toReal hmin_ne]; exact min_le_left _ _
  obtain ⟨c, hc⟩ := hSB (max t 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) δr hδr_pos
  set c' := max c 0
  have hev : ∀ᶠ n in atTop, c' / ε + 1 ≤ a n ∧ 1 ≤ n :=
    (hlim.eventually (eventually_ge_atTop (c' / ε + 1))).and (eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨han, hn1⟩ := hN n hn
  have hapos : 0 < a n := ha n hn1
  refine le_trans ?_ (le_trans (hc n hn1) hδr_le)
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push_neg at hcon
  -- supDist (X n ω) 0 (max t 1) ≤ ofReal c ≤ ofReal c'
  have hX : ∀ s ∈ Set.Icc (0:ℝ) t, (∑ i, |X n ω s i - (0 : ℝ → Fin k → ℝ) s i|) ≤ c' := by
    intro s hs
    have h1 : ENNReal.ofReal (∑ i, |X n ω s i - (0 : ℝ → Fin k → ℝ) s i|)
        ≤ supDist (X n ω) 0 (max t 1) := by
      unfold supDist
      exact le_iSup₂_of_le (f := fun (s : ℝ) (_ : s ∈ Set.Icc 0 (max t 1)) =>
        ENNReal.ofReal (∑ i, |X n ω s i - (0 : ℝ → Fin k → ℝ) s i|)) s
        ⟨hs.1, le_trans hs.2 (le_max_left _ _)⟩ le_rfl
    have h2 := le_trans h1 (le_trans hcon (ENNReal.ofReal_le_ofReal (le_max_left c 0)))
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right c 0)).1 h2
  have hlt : supDist (fun t => (a n)⁻¹ • X n ω t) (fun _ => 0) t < ENNReal.ofReal ε := by
    have hbound : supDist (fun t => (a n)⁻¹ • X n ω t) (fun _ => 0) t
        ≤ ENNReal.ofReal ((a n)⁻¹ * c') := by
      unfold supDist
      refine iSup₂_le fun s hs => ENNReal.ofReal_le_ofReal ?_
      have := hX s hs
      simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_inv, abs_of_pos hapos] at this ⊢
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hapos.le)
    refine lt_of_le_of_lt hbound ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    rw [inv_mul_lt_iff₀ hapos]
    have : c' / ε < a n := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  exact absurd hω (not_le.2 hlt)
