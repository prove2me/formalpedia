-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_step_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:16:14.169051+00:00
-- url     : https://prove2.me/submissions/f5d6458c-5e6a-4748-bd97-125733ee1f73

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_threshold_transfer
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
    let E : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → ℕ → NNReal → ℝ :=
      fun m b c n t => ∑ i ∈ Finset.range m, c i * D n (b i) t
    (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t| < e) →
      ∀ (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ) (e : ℝ), 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |E m b c (N n) t| < e := by
  intro A F D E hA m b c e he
  let C : ℝ := (∑ i ∈ Finset.range m, |c i|)+1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := e/(2*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have h (i : ℕ) : ∀ᶠ n in atTop, ∀ t ≤ T, |D (N n) (b i) t| < δ :=
    ito43_qv_threshold_transfer X Xleft w hc hl σ hσ g hg T hs N hN hA (b i) δ hδ
  have hfin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range m, ∀ t ≤ T,
      |D (N n) (b i) t| < δ :=
    (Finset.eventually_all _).mpr (fun i _ => h i)
  filter_upwards [hfin] with n hn
  intro t ht
  change |∑ i ∈ Finset.range m, c i * D (N n) (b i) t| < e
  have hb : |∑ i ∈ Finset.range m, c i * D (N n) (b i) t| ≤
      ∑ i ∈ Finset.range m, |c i| * δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hn i hi t ht).le (abs_nonneg _)
  rw [← Finset.sum_mul] at hb
  have hC' : (∑ i ∈ Finset.range m, |c i|) ≤ C := by dsimp [C]; linarith
  have h := mul_le_mul_of_nonneg_right hC' hδ.le
  have heq : C*δ = e/2 := by dsimp [δ]; field_simp
  rw [heq] at h
  linarith
