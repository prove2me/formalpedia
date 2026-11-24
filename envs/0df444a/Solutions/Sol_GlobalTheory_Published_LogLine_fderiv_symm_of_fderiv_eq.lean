-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.fderiv_symm_of_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:08.460529+00:00
-- url     : https://prove2.me/submissions/f310249e-5f59-4a7b-8c6d-67c273dee406

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_SCV_contDiffAt_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {β : (Fin n → ℂ) → (Fin n → ℂ) →L[ℂ] ℂ} {f : (Fin n → ℂ) → ℂ}
    (hβ : DifferentiableOn ℂ β V) (hf : DifferentiableOn ℂ f V) (hne : ∀ z ∈ V, f z ≠ 0)
    (h : ∀ z ∈ V, fderiv ℂ f z = -(f z • β z)) {z : Fin n → ℂ} (hz : z ∈ V) (x y : Fin n → ℂ) :
    fderiv ℂ β z x y = fderiv ℂ β z y x := by
  have hn := hV.mem_nhds hz
  have hs : IsSymmSndFDerivAt ℂ f z :=
    (GlobalTheory.SCV.contDiffAt_of_differentiableOn hf hn 2).isSymmSndFDerivAt (by simp)
  have he : fderiv ℂ f =ᶠ[𝓝 z] fun w => -(f w • β w) := by
    filter_upwards [hn] with w hw using h w hw
  have h1 := ((hf.differentiableAt hn).hasFDerivAt.smul (hβ.differentiableAt hn).hasFDerivAt).neg
  have h2 : fderiv ℂ (fderiv ℂ f) z = _ := he.fderiv_eq.trans h1.fderiv
  have h3 := hs x y
  rw [h2, h z hz] at h3
  simp at h3
  have := hne z hz
  apply mul_left_cancel₀ this
  linear_combination -h3
end GlobalTheory.Published.LogLine
