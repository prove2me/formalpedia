-- Prove2me | solution 1 for InfoRelaxTS.Asymptotic.display_109
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:25:27.247756+00:00
-- url     : https://prove2.me/submissions/0a93ced5-ee3b-4d1c-8d04-ed53267f7743

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open InfoRelaxTS InfoRelaxTS.Asymptotic

theorem solution {K : ℕ} [NeZero K] (sel : (Fin K → ℝ) → Fin K) (hsel : Gap.IsArgmaxSel sel)
    (m : ℕ → Fin K → ℝ) (v : Fin K → ℝ) (hv : Function.Injective v)
    (hm : ∀ a, Tendsto (fun n => m n a) atTop (𝓝 (v a))) :
    ∀ᶠ n in atTop, sel (m n) = sel v := by
  set b := sel v with hb
  have hgap : ∀ c, c ≠ b → v c < v b := by
    intro c hc
    exact lt_of_le_of_ne (hsel v c) (fun h => hc (hv h))
  have hev : ∀ c, ∀ᶠ n in atTop, c ≠ b → m n c < m n b := by
    intro c
    by_cases hc : c = b
    · exact Eventually.of_forall fun _ h => absurd hc h
    · have h1 : Tendsto (fun n => m n b - m n c) atTop (𝓝 (v b - v c)) :=
        (hm b).sub (hm c)
      have h2 : (0:ℝ) < v b - v c := sub_pos.mpr (hgap c hc)
      filter_upwards [h1.eventually (lt_mem_nhds h2)] with n hn _
      linarith
  filter_upwards [eventually_all.mpr hev] with n hn
  by_contra hne
  have h1 := hn (sel (m n)) hne
  have h2 := hsel (m n) b
  linarith
