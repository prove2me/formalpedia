-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_4_esscher_shifted_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:38:10.384621+00:00
-- url     : https://prove2.me/submissions/e9d48b8b-120b-488e-a15c-ba46efa8621d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution
    (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (c : ℝ)
    (hc : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P) :
    IsEsscherLaplaceShifted P D ψ c := by
  intro β t hβ ht hInt
  let I : ℝ := ∫ ω, Real.exp ((c + β) * D.X t ω) ∂P
  have hMoment := hψ.2 (c + β) t ht hInt
  have hMoment' : 0 < I ∧ ψ (c + β) = Real.log I / (t : ℝ) := by
    simpa [I, SpectrallyNegativeModel.toData] using hMoment
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htRne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have hLog : (t : ℝ) * ψ (c + β) = Real.log I := by
    rw [hMoment'.2]
    field_simp [htRne]
  have hIexp : I = Real.exp (Real.log I) :=
    (Real.exp_log hMoment'.1).symm
  have hIntegrand :
      (fun ω => Real.exp (β * D.X t ω) *
        esscherDensity (SpectrallyNegativeModel.toData P D) ψ c t ω) =
      (fun ω => Real.exp (-(ψ c * (t : ℝ))) *
        Real.exp ((c + β) * D.X t ω)) := by
    funext ω
    simp only [esscherDensity, SpectrallyNegativeModel.toData]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (∫ ω, Real.exp (β * D.X t ω) *
      esscherDensity (SpectrallyNegativeModel.toData P D) ψ c t ω ∂P) =
        ∫ ω, Real.exp (-(ψ c * (t : ℝ))) *
          Real.exp ((c + β) * D.X t ω) ∂P := by rw [hIntegrand]
    _ = Real.exp (-(ψ c * (t : ℝ))) * I := by
      simp only [I, integral_const_mul]
    _ = Real.exp ((t : ℝ) * shiftedExponent ψ c β) := by
      rw [hIexp, ← Real.exp_add]
      congr 1
      rw [← hLog, shiftedExponent]
      rw [add_comm β c]
      ring
