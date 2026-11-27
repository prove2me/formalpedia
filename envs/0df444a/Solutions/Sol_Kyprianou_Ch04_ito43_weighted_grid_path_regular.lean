-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_grid_path_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:21:28.173807+00:00
-- url     : https://prove2.me/submissions/cc218ccc-277c-4de8-8f11-a39befcbe0bb

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_sum_regular
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (n : ℕ) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let Q : NNReal → ℝ := fun t => ∑ k ∈ Finset.range n,
      g ((u k:ℝ),X (u k) w)*(X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
    (∀ t, ContinuousWithinAt Q (Ici t) t) ∧ ∃ M : ℝ, ∀ t ≤ T, |Q t| ≤ M := by
  intro u Q
  let F : ℕ → NNReal → ℝ := fun k t =>
    g ((u k:ℝ),X (u k) w)*(X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
  have hc' (a t : NNReal) : ContinuousWithinAt (fun s => X (min s a) w) (Ici t) t := by
    have hm : Continuous (fun s : NNReal => min s a) := continuous_id.min continuous_const
    have hmap : MapsTo (fun s : NNReal => min s a) (Ici t) (Ici (min t a)) := by
      intro s hs
      change min t a ≤ min s a
      exact min_le_min (show t ≤ s from hs) le_rfl
    exact (hc (min t a)).1.comp (f := fun s : NNReal => min s a)
      hm.continuousWithinAt hmap
  obtain ⟨_,R,hR,hX,_⟩ := exercise41PathCompactV10 X L w hc hl T
  apply ito43_cutoff_finite_sum_regular (Finset.range n) F T
  · intro k hk t
    exact (continuousWithinAt_const.mul (((hc' (u (k+1)) t).sub (hc' (u k) t)).pow 2)).div_const 2
  · intro k hk
    let M : ℝ := |g ((u k:ℝ),X (u k) w)| * (2*R)^2/2
    refine ⟨M,fun t ht => ?_⟩
    have ha := hX (min t (u (k+1))) ((min_le_left _ _).trans ht)
    have hb := hX (min t (u k)) ((min_le_left _ _).trans ht)
    let z := X (min t (u (k+1))) w-X (min t (u k)) w
    have hz : |z| ≤ 2*R := by
      have h := abs_sub_le (X (min t (u (k+1))) w) 0 (X (min t (u k)) w)
      simp only [sub_zero,zero_sub,abs_neg] at h
      exact h.trans (by linarith)
    have hsq : z^2 ≤ (2*R)^2 := by nlinarith [abs_le.mp hz]
    dsimp only [F]
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg z),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    dsimp [M]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)) (by norm_num)
