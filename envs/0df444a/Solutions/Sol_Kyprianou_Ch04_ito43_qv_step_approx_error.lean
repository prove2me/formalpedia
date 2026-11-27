-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_step_approx_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:39:21.0738+00:00
-- url     : https://prove2.me/submissions/4fd10baf-1a61-4ba2-8527-b566c18a1b78

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_unweighted_path_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_pointwise_bound
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
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
    let B : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      σ *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      g (z.1,Xleft (Real.toNNReal z.1) w) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft w)) - (∑ k ∈ Finset.range n,
      g ((u k : ℝ), X (u k) w) * (X (v (k+1)) w - X (v k) w)^2 / 2)
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
    (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t| < e) →
      ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ),
        0 < δ →
        (∀ s ≤ T, |g ((s:ℝ),X s w)-W m b c s| ≤ δ) →
        (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),Xleft s w)-L m b c s| ≤ δ) →
        ∀ᶠ n in atTop, ∀ t ≤ T, |B (N n) t-E m b c (N n) t| ≤ C*δ := by
  intro A B F D E W L
  intro hA
  let J : ℝ := (1/2)*(∑' s : Ioc (0:NNReal) (T+1), (X s w-Xleft s w)^2)
  let M : ℝ := σ*(T:ℝ)+J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => sq_nonneg _))
  have hM : 0 ≤ M := add_nonneg (mul_nonneg hσ T.coe_nonneg) hJ
  have hJcount := exercise41CadlagPhysicalJumpsCountableV17 (fun s => X s w)
    (fun s => Xleft s w) (fun s => (hc s).1) hl
  refine ⟨2*M+1,by linarith only [hM],?_⟩
  intro δ m b c hδ hW hL
  filter_upwards [hA 1 zero_lt_one] with n hn
  intro t ht
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(N n:NNReal)
  let v : ℕ → NNReal := fun k => min t (u k)
  let Q : ℝ := ∑ k ∈ Finset.range (N n), (X (v (k+1)) w-X (v k) w)^2/2
  have hF : F t ≤ M := ito43_qv_unweighted_path_bound X Xleft w hJcount
    (T+1) T t ht (by simp) hs σ hσ
  have hAn : |F t-Q| < 1 := hn t ht
  have hQ : Q ≤ M+1 := by linarith only [(abs_lt.mp hAn).1,hF]
  have hp := ito43_qv_step_pointwise_bound X Xleft w hc hl σ hσ g hg T hs
    δ m b c hδ hW hL (N n) t ht
  calc
    |B (N n) t-E m b c (N n) t| ≤ δ*(M+Q) := hp
    _ ≤ δ*(M+(M+1)) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hQ) hδ.le
    _ = (2*M+1)*δ := by ring
