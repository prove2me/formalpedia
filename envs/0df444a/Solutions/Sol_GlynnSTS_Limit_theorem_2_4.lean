-- Prove2me | solution 1 for GlynnSTS.Limit.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:43:08.684529+00:00
-- url     : https://prove2.me/submissions/cf3398fc-19cc-403d-a45e-729508707b9a

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_GlynnSTS_Limit_hmap_Xn_tendsto
import Theorems.Thm_GlynnSTS_Limit_hmap_sigmaB
import Theorems.Thm_GlynnSTS_Limit_hmap_Xn_eq

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

open GlynnSTS.Limit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ σ : ℝ)
    (h21 : Assumption21 P Y Ybar μ σ B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) :
    TendstoInDistribution (fun (n : ℕ) ω => (Ybar n ω 1 - μ) / g (Ybar n ω)) atTop
      (fun ω => B ω 1 / g (B ω)) (fun _ => P) P := by
  obtain ⟨_, hhom, hshift, _, _⟩ := id hg
  -- `g 0 = 0` by positive homogeneity
  have hg0 : g 0 = 0 := by
    have := hhom 2 (by norm_num) 0
    rw [smul_zero] at this
    linarith
  have heq : ∀ n : ℕ, ∀ ω, hmap g (Xn Ybar μ n ω) = (Ybar n ω 1 - μ) / g (Ybar n ω) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hY0 : Ybar 0 ω = 0 := by
        ext t
        rw [h21.ybar_eq 0 ω t]
        simp
      have hX0 : Xn Ybar μ 0 ω = 0 := by
        simp [Xn]
      rw [hX0, hY0, hg0]
      simp [hmap, hg0]
    · exact hmap_Xn_eq Ybar μ g hhom hshift n hn ω
  have hT := hmap_Xn_tendsto P B hB Y Ybar μ σ h21 g hg
  refine hT.congr (fun n => Filter.Eventually.of_forall (fun ω => heq n ω))
    (Filter.Eventually.of_forall (fun ω => hmap_sigmaB B g hhom σ h21.sigma_pos ω))
