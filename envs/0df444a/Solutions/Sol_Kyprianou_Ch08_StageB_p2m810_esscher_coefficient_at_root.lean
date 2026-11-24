-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_esscher_coefficient_at_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:01:31.259997+00:00
-- url     : https://prove2.me/submissions/d99942df-952f-4b56-8bb2-ed884f1efe7d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_differentiable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    esscherDownCoefficient ψ (Phi ψ q) q = deriv ψ (Phi ψ q) := by
  have hr := (hW q hq.le).1.2.1
  have hroot : ψ (Phi ψ q) = q := hr.2
  obtain ⟨hp, hi⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hD := (p2m89_phi_differentiable Ω P D ψ W hψ hW q hq).hasDerivAt
  have hs := (hasDerivAt_iff_tendsto_slope_zero.mp hD).mono_left
    (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun t ht => (mem_Ioi.mp ht).ne'))
  have hsec : Tendsto (fun h : ℝ => (Phi ψ (h+q)-Phi ψ q)/h)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (deriv (Phi ψ) q)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, add_comm] using hs
  have hne : deriv (Phi ψ) q ≠ 0 := by rw [hi]; exact inv_ne_zero hp.ne'
  have hlim : Tendsto (fun h : ℝ => h/(Phi ψ (h + ψ (Phi ψ q)) - Phi ψ q))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (deriv ψ (Phi ψ q))) := by
    simpa only [hroot, inv_div, hi, inv_inv] using hsec.inv₀ hne
  unfold esscherDownCoefficient
  rw [if_pos hroot.symm]
  have h := Classical.epsilon_spec (p := fun L : ℝ =>
    Tendsto (fun h : ℝ => h / (Phi ψ (h + ψ (Phi ψ q)) - Phi ψ q))
      (nhdsWithin 0 (Ioi 0)) (𝓝 L)) ⟨_, hlim⟩
  exact tendsto_nhds_unique h hlim
