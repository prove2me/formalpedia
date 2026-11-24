-- Prove2me | solution 1 for GlobalTheory.GaussWidths.hasWidth_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:22.426529+00:00
-- url     : https://prove2.me/submissions/60f5b2d5-8ec8-4299-840f-ce3fe9bcbd54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GlobalTheory_GaussWidths_exists_schwartz_gauss_width
import Theorems.Thm_GlobalTheory_GaussWidths_mem_of_smul
import Theorems.Thm_GlobalTheory_GaussWidths_integral_gauss_mul_gauss
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
theorem _root_.solution {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM
end GlobalTheory.GaussWidths
