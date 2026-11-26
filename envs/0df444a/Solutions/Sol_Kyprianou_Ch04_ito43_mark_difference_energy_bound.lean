-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_difference_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:25:33.505331+00:00
-- url     : https://prove2.me/submissions/225ac26b-de45-46b0-83fa-05021d8eb76f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_combined_error_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (H T : NNReal) (hTH : T ≤ H)
    (hJ : Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2))
    (r c : ℝ → ℝ) (C e : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hr : ∀ z, |r z| ≤ C*z^2) (hc' : ∀ z, |c z| ≤ C*z^2)
    (hd : ∀ z, |r z-c z| ≤ e*z^2) :
    ∀ (n : ℕ) (t : NNReal), t ≤ T →
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let B : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ univ
    let d : ℕ → ℝ := fun k => X (v (k+1)) w-X (v k) w
    |((∫ z in B, r z.2 ∂(pathJumpMeasure X L w)) - ∑ k ∈ Finset.range n, r (d k)) -
      ((∫ z in B, c z.2 ∂(pathJumpMeasure X L w)) - ∑ k ∈ Finset.range n, c (d k))| ≤
        e*((∑ k ∈ Finset.range n, (d k)^2) + ∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2) := by
  intro n t ht u v B d
  have hcount := Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
    (fun s => X s w) (fun s => L s w) (fun s => (hc s).1) hl
  have hbound (f : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, |f z| ≤ K*z^2) :=
    Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X L w hcount H t (ht.trans hTH)
      K hK hJ (fun z => f z.2) (fun s _ _ => hf (X s w-L s w))
  have hi := (hbound r C hC hr).1
  have hci := (hbound c C hC hc').1
  have hj := (hbound (fun z => r z-c z) e he hd).2
  let μ := (pathJumpMeasure X L w).restrict B
  change Integrable (fun z : ℝ × ℝ => r z.2) μ at hi
  change Integrable (fun z : ℝ × ℝ => c z.2) μ at hci
  have hji : |(∫ z, r z.2 ∂μ)-(∫ z, c z.2 ∂μ)| ≤
      e*(∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2) := by
    rw [← integral_sub hi hci]
    exact hj
  have hg : |(∑ k ∈ Finset.range n, r (d k)) - ∑ k ∈ Finset.range n, c (d k)| ≤
      e*∑ k ∈ Finset.range n, (d k)^2 := by
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hd (d k)))
  change |((∫ z, r z.2 ∂μ) - ∑ k ∈ Finset.range n, r (d k)) -
    ((∫ z, c z.2 ∂μ) - ∑ k ∈ Finset.range n, c (d k))| ≤ _
  have h := abs_sub_le ((∫ z, r z.2 ∂μ)-(∫ z, c z.2 ∂μ)) 0
    ((∑ k ∈ Finset.range n, r (d k)) - ∑ k ∈ Finset.range n, c (d k))
  simp only [sub_zero,zero_sub,abs_neg] at h
  rw [show ((∫ z, r z.2 ∂μ) - ∑ k ∈ Finset.range n, r (d k)) -
    ((∫ z, c z.2 ∂μ) - ∑ k ∈ Finset.range n, c (d k)) =
    ((∫ z, r z.2 ∂μ)-(∫ z, c z.2 ∂μ)) -
      ((∑ k ∈ Finset.range n, r (d k)) - ∑ k ∈ Finset.range n, c (d k)) by ring]
  exact h.trans ((add_le_add hji hg).trans (by ring_nf; rfl))
