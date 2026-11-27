-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_step_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:42:08.909225+00:00
-- url     : https://prove2.me/submissions/3d4c7ac1-4b59-4d7b-a293-384c35084c65

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_path_step_error
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_jump_step_error
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_grid_step_error
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_residual_combine
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
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2)) :
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
    let Q : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2/2
    ∀ (δ : ℝ) (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ),
      0 < δ →
      (∀ s ≤ T, |g ((s:ℝ),X s w)-W m b c s| ≤ δ) →
      (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),Xleft s w)-L m b c s| ≤ δ) →
      ∀ (n : ℕ) (t : NNReal), t ≤ T →
        |B n t-E m b c n t| ≤ δ*(σ*(T:ℝ) +
          (1/2)*(∑' s : Ioc (0:NNReal) (T+1), (X s w-Xleft s w)^2) + Q n t) := by
  intro B F D E W L Q
  intro δ m b c hδ hW hL n t ht
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
  let v : ℕ → NNReal := fun k => min t (u k)
  let en : ℕ → ℝ := fun k => (X (v (k+1)) w-X (v k) w)^2/2
  let Y : ℝ → ℝ := fun s => g (s,X s.toNNReal w)
  let J : ℝ := (1/2)*(∑' s : Ioc (0:NNReal) (T+1), (X s w-Xleft s w)^2)
  let A0 : ℝ := ∫ s in Icc (0:ℝ) (t:ℝ), Y s ∂volume
  let B0 : ℝ := ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
    g (z.1,Xleft z.1.toNNReal w)*(z.2^2/2) ∂(pathJumpMeasure X Xleft w)
  let G0 : ℝ := ∑ k ∈ Finset.range n, g ((u k:ℝ),X (u k) w)*en k
  let a : ℕ → ℝ := fun i => (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
    ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume
  let j : ℕ → ℝ := fun i =>
    (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂(pathJumpMeasure X Xleft w)) -
    ∫ z in Icc (0:ℝ) ((min t (b i):NNReal):ℝ) ×ˢ (univ : Set ℝ),
      z.2^2/2 ∂(pathJumpMeasure X Xleft w)
  let q : ℕ → ℝ := fun i => ∑ k ∈ Finset.range n,
    (if b i ≤ u k then (1:ℝ) else 0)*en k
  have htime : |A0-∑ i ∈ Finset.range m, c i*a i| ≤ δ*(T:ℝ) :=
    ito43_qv_time_path_step_error X Xleft w hc hl g hg T t ht δ hδ.le m b c hW
  have hJcount := exercise41CadlagPhysicalJumpsCountableV17 (fun s => X s w)
    (fun s => Xleft s w) (fun s => (hc s).1) hl
  have hjump := ito43_qv_jump_step_error X Xleft w hJcount (T+1) t
    (ht.trans (by simp)) hs g δ hδ.le m b c (fun s hs0 hst => hL s hs0 (hst.trans ht))
  have hjump' : |B0-∑ i ∈ Finset.range m, c i*j i| ≤ δ*J := by
    calc
      _ ≤ (δ/2)*(∑' s : Ioc (0:NNReal) (T+1), (X s w-Xleft s w)^2) := hjump
      _ = _ := by dsimp [J]; ring
  have hu : ∀ k < n, u k ≤ T := by
    intro k hk
    have hn : 0 < (n:NNReal) := by exact_mod_cast Nat.zero_lt_of_lt hk
    have hkn : (k:NNReal) ≤ (n:NNReal) := by exact_mod_cast hk.le
    dsimp [u]
    exact (div_le_iff₀ hn).2 (mul_le_mul_of_nonneg_left hkn zero_le)
  have hgrid : |G0-∑ i ∈ Finset.range m, c i*q i| ≤ δ*Q n t :=
    ito43_qv_grid_step_error n m u T hu (fun s => g ((s:ℝ),X s w)) en
      (fun k _ => by dsimp [en]; positivity) δ b c hW
  have hcombine := ito43_qv_step_residual_combine σ δ (T:ℝ) J (Q n t)
    A0 B0 G0 hσ m c a j q htime hjump' hgrid
  have hB : B n t = σ*A0+B0-G0 := by
    simp only [B,A0,B0,G0,Y,u,v,en,mul_div_assoc] <;> rfl
  have hE : E m b c n t = ∑ i ∈ Finset.range m, c i*(σ*a i+j i-q i) := by
    dsimp only [E]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [D,F,a,j,q,u,v,en]
    simp only [mul_div_assoc]
    ring
  rw [hB,hE]
  exact hcombine
