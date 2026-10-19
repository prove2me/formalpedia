-- Prove2me | solution 1 for OAI.EntropyRateDimension.Interpolation.tendsto_div_of_bounded_gaps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:07:46.390696+00:00
-- url     : https://prove2.me/submissions/ceb9e5fb-41bd-4a0c-a9ec-c57ff4380478

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology


theorem solution {F : ℝ → ℝ} {t : ℕ → ℝ} {C d : ℝ}
    (hF : Monotone F) (ht : Monotone t) (ht0 : t 0 = 0)
    (hstep : ∀ n, t (n+1) ≤ t n+C) (htop : Tendsto t atTop atTop)
    (hlim : Tendsto (fun n => F (t n) / t n) atTop (𝓝 d)) :
    Tendsto (fun s => F s / s) atTop (𝓝 d) := by
  have hex : ∀ s : ℝ, ∃ n, s < t (n+1) := fun s => by
    obtain ⟨n, hn⟩ := (htop.eventually_gt_atTop s).exists
    exact ⟨n, lt_of_lt_of_le hn (ht (Nat.le_succ n))⟩
  obtain ⟨N, hN1, hN0⟩ : ∃ N : ℝ → ℕ, (∀ s, s < t (N s + 1)) ∧ (∀ s, 0 ≤ s → t (N s) ≤ s) := by
    classical
    refine ⟨fun s => Nat.find (hex s), fun s => Nat.find_spec (hex s), fun s hs => ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find (hex s)) with h | h
    · simp only [h, ht0]; exact hs
    · have := Nat.find_min (hex s) (Nat.sub_lt h one_pos)
      have e : Nat.find (hex s) - 1 + 1 = Nat.find (hex s) := by omega
      rw [e] at this
      exact not_lt.mp this
  have hNt : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    filter_upwards [eventually_ge_atTop (t M)] with s hs
    by_contra hlt
    push_neg at hlt
    have := ht (Nat.succ_le_of_lt hlt)
    linarith [hN1 s]
  have hA : Tendsto (fun s => F (t (N s)) / t (N s)) atTop (𝓝 d) := hlim.comp hNt
  have hB : Tendsto (fun s => F (t (N s + 1)) / t (N s + 1)) atTop (𝓝 d) :=
    (hlim.comp (tendsto_add_atTop_nat 1)).comp hNt
  have hCs : Tendsto (fun s : ℝ => C / s) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have htN : Tendsto (fun s => t (N s)) atTop atTop := htop.comp hNt
  have hev : ∀ᶠ s in atTop, 0 < s ∧ 0 < t (N s) := by
    filter_upwards [eventually_gt_atTop (0:ℝ), htN.eventually_gt_atTop 0] with s h1 h2
    exact ⟨h1, h2⟩
  have hr1 : Tendsto (fun s => t (N s) / s) atTop (𝓝 1) := by
    have hl : Tendsto (fun s : ℝ => 1 - C / s) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hCs
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    · filter_upwards [hev] with s ⟨hs, _⟩
      have h1 := hN1 s
      have h2 := hstep (N s)
      rw [one_sub_div hs.ne', div_le_div_iff_of_pos_right hs]
      linarith
    · filter_upwards [hev] with s ⟨hs, _⟩
      rw [div_le_one hs]; exact hN0 s hs.le
  have hr2 : Tendsto (fun s => t (N s + 1) / s) atTop (𝓝 1) := by
    have hu : Tendsto (fun s : ℝ => 1 + C / s) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add hCs
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [hev] with s ⟨hs, _⟩
      rw [le_div_iff₀ hs, one_mul]; exact (hN1 s).le
    · filter_upwards [hev] with s ⟨hs, _⟩
      have h1 := hN0 s hs.le
      have h2 := hstep (N s)
      rw [one_add_div hs.ne', div_le_div_iff_of_pos_right hs]
      linarith
  have hg1 : Tendsto (fun s => F (t (N s)) / t (N s) * (t (N s) / s)) atTop (𝓝 d) := by
    simpa using hA.mul hr1
  have hg2 : Tendsto (fun s => F (t (N s + 1)) / t (N s + 1) * (t (N s + 1) / s)) atTop (𝓝 d) := by
    simpa using hB.mul hr2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg1 hg2
  · filter_upwards [hev] with s ⟨hs, htn⟩
    rw [div_mul_div_cancel₀ htn.ne']
    exact div_le_div_of_nonneg_right (hF (hN0 s hs.le)) hs.le
  · filter_upwards [hev] with s ⟨hs, htn⟩
    have htn1 : 0 < t (N s + 1) := lt_of_lt_of_le htn (ht (Nat.le_succ _))
    rw [div_mul_div_cancel₀ htn1.ne']
    exact div_le_div_of_nonneg_right (hF (hN1 s).le) hs.le

