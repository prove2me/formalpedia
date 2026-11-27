-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_threshold_crossing_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:21:28.220586+00:00
-- url     : https://prove2.me/submissions/1bbdcbd9-4c5d-4081-bea7-156068956244

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_threshold_grid_error_bound
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
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
    let Q : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2/2
    ∀ b : NNReal, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T,
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(N n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      |Q (N n) t-Q (N n) (min t b) -
        ∑ k ∈ Finset.range (N n), (if b ≤ u k then (1:ℝ) else 0) *
          (X (v (k+1)) w-X (v k) w)^2/2| < e := by
  intro Q b e he
  obtain ⟨_,R,hR,hX,_⟩ := exercise41PathCompactV10 X Xleft w hc hl T
  let δ := e/(4*R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r,hr,hright⟩ := (Metric.continuousWithinAt_iff.mp (hc b).1) δ hδ
  have hmesh : Tendsto (fun n => (T:ℝ)/(N n:ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (T:ℝ)).comp hN
  have hpos : ∀ᶠ n in atTop, 0 < N n := hN.eventually (eventually_gt_atTop (0:ℕ))
  filter_upwards [hmesh.eventually (Iio_mem_nhds hr),hpos] with n hn hn0
  intro t ht
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(N n:NNReal)
  have hu : Monotone u := by intro i j hij; dsimp [u]; gcongr
  have hp (k : ℕ) (hk : k < N n) (hbt : b ≤ t) (hkb : u k < b) (hbk : b < u (k+1)) :
      |X (min t (u (k+1))) w-X b w| ≤ δ := by
    have hmin : b ≤ min t (u (k+1)) := le_min hbt hbk.le
    have hgap : (u (k+1):ℝ)-(u k:ℝ) = (T:ℝ)/(N n:ℝ) := by
      dsimp [u]
      push_cast
      ring
    have hd : dist (min t (u (k+1))) b < r := by
      change dist ((min t (u (k+1)):NNReal):ℝ) (b:ℝ) < r
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmin))]
      have h1 : ((min t (u (k+1)):NNReal):ℝ) ≤ (u (k+1):ℝ) := by exact_mod_cast min_le_right t (u (k+1))
      have h2 : (u k:ℝ) ≤ (b:ℝ) := by exact_mod_cast hkb.le
      linarith
    exact le_of_lt (by simpa only [Real.dist_eq] using hright hmin hd)
  have h := ito43_threshold_grid_error_bound (fun s => X s w) u hu (N n) b t T ht R δ
    hR.le hδ.le hX hp
  have heq : 2*R*δ = e/2 := by dsimp [δ]; field_simp <;> ring
  rw [heq] at h
  exact h.trans_lt (by linarith)
