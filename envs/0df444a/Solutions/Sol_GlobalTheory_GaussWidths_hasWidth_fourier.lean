-- Prove2me | solution 1 for GlobalTheory.GaussWidths.hasWidth_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:13.163147+00:00
-- url     : https://prove2.me/submissions/2ab1d267-ec81-41e5-bb9e-b484390bdc1e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GlobalTheory_GaussWidths_exists_schwartz_gauss_width
import Theorems.Thm_GlobalTheory_GaussWidths_mem_of_smul
import Theorems.Thm_GlobalTheory_GaussWidths_cpow_ne_zero_of_pos
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory.GaussWidths
theorem _root_.solution {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
end GlobalTheory.GaussWidths
