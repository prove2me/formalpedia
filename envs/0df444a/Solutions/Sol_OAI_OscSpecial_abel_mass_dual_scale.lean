-- Prove2me | solution 1 for OAI.OscSpecial.abel_mass_dual_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:06.828848+00:00
-- url     : https://prove2.me/submissions/fd88cc35-c047-4b3f-9204-990444889fa7

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_OscSpecial_dualScale_tendsto
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.OscSpecial
open scoped Topology
open Filter
namespace OAI.OscSpecial
theorem _root_.solution (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)
end OAI.OscSpecial
