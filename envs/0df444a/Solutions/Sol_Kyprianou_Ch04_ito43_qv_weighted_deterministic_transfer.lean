-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_weighted_deterministic_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:18:51.393662+00:00
-- url     : https://prove2.me/submissions/ca6f78ca-dd43-4ad0-b88a-a0218b137163

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_step_pair_approx
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_transfer
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_approx_error
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
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
    let B : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      σ *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      g (z.1,Xleft (Real.toNNReal z.1) w) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft w)) - (∑ k ∈ Finset.range n,
      g ((u k : ℝ), X (u k) w) * (X (v (k+1)) w - X (v k) w)^2 / 2)
    (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t| < e) →
      ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |B (N n) t| < e := by
  intro A B hA e he
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
  let W : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
    fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)
  let L : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
    fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)
  obtain ⟨C,hC,herr⟩ := ito43_qv_step_approx_error X Xleft w hc hl σ hσ g hg T hs N hN hA
  let δ := e/(2*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m,b,c,hW,hL⟩ := ito43_weighted_step_pair_approx X Xleft w hc hl σ hσ g hg T hs δ hδ
  have h1 := herr δ m b c hδ hW hL
  have h2 := ito43_qv_step_transfer X Xleft w hc hl σ hσ g hg T hs N hN hA
    m b c (e/2) (by positivity)
  filter_upwards [h1,h2] with n hn hn'
  intro t ht
  have h3 := hn t ht
  have h4 := hn' t ht
  have heq : C*δ = e/2 := by dsimp [δ]; field_simp
  rw [heq] at h3
  have h5 := abs_sub_le (B (N n) t) (E m b c (N n) t) 0
  simp only [sub_zero] at h5
  linarith
