-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_threshold_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:16:14.176631+00:00
-- url     : https://prove2.me/submissions/1135a0ad-7ab0-490e-9543-6c565bc8175f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_threshold_crossing_error
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution  {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (w : Omega)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t w)))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (T : NNReal)
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    let A : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      σ *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      z.2^2 / 2 ∂(pathJumpMeasure X Xleft w)) - (∑ k ∈ Finset.range n,
      (X (v (k+1)) w - X (v k) w)^2 / 2)
    let F : NNReal → ℝ := fun t =>
      σ * (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) +
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂(pathJumpMeasure X Xleft w)
    let D : ℕ → NNReal → NNReal → ℝ := fun n b t =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      F t-F (min t b) -
        ∑ k ∈ Finset.range n, (if b ≤ u k then (1:ℝ) else 0) *
          (X (v (k+1)) w-X (v k) w)^2/2
    (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t| < e) →
      ∀ b : NNReal, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T,
        |D (N n) b t| < e := by
  intro A F D hA b e he
  have hcross := ito43_qv_threshold_crossing_error X Xleft w hc hl σ hσ g hg T hs N hN
    b (e/3) (by positivity)
  filter_upwards [hA (e/3) (by positivity),hcross] with n hn hcn
  intro t ht
  have h1 := hn t ht
  have h2 := hn (min t b) ((min_le_left _ _).trans ht)
  have h3 := hcn t ht
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(N n:NNReal)
  let Q : NNReal → ℝ := fun t => ∑ k ∈ Finset.range (N n),
    (X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
  let R : ℝ := ∑ k ∈ Finset.range (N n), (if b ≤ u k then (1:ℝ) else 0) *
    (X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
  change |Q t-Q (min t b)-R| < e/3 at h3
  have heq : D (N n) b t = A (N n) t-A (N n) (min t b)+(Q t-Q (min t b)-R) := by
    change F t-F (min t b)-R = (F t-Q t)-(F (min t b)-Q (min t b))+(Q t-Q (min t b)-R)
    ring
  rw [heq]
  have h4 := abs_sub_le (A (N n) t) 0 (A (N n) (min t b))
  simp only [sub_zero,zero_sub,abs_neg] at h4
  linarith [abs_add_le (A (N n) t-A (N n) (min t b)) (Q t-Q (min t b)-R)]
