-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.uniformisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:25.133679+00:00
-- url     : https://prove2.me/submissions/6c4bbbbd-91df-4a36-aaec-e1204a533133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
import Theorems.Thm_GlobalTheory_DiscUniformisation_E_cube_ne
import Theorems.Thm_GlobalTheory_DiscUniformisation_exists_ratio
import Theorems.Thm_GlobalTheory_DiscUniformisation_exists_scale
import Theorems.Thm_GlobalTheory_DiscUniformisation_g_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (a b : ℂ) (h : a ^ 3 ≠ 27 * b ^ 2) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  have hAB : (3 / 4 * a) ^ 3 ≠ (27 / 8 * b) ^ 2 := by
    intro hc
    apply h
    linear_combination (64 / 27) * hc
  obtain ⟨z, hz⟩ := exists_ratio (3 / 4 * a) (27 / 8 * b) hAB
  obtain ⟨μ, hμ0, hμ4, hμ6⟩ := exists_scale (3 / 4 * a) (27 / 8 * b) (E₄ z) (E₆ z) hAB (E_cube_ne z) hz
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (Real.pi : ℂ) / μ ≠ 0 := div_ne_zero hπ hμ0
  have hzim : 0 < (z : ℂ).im := by simpa using z.im_pos
  have hind : LinearIndependent ℝ ![(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    rw [Complex.real_smul, Complex.real_smul] at hst
    have h1 : ((s : ℂ) * z + t) * ((Real.pi : ℂ) / μ) = 0 := by linear_combination hst
    have h2 : (s : ℂ) * z + t = 0 := (mul_eq_zero.1 h1).resolve_right hω
    have h3 : s * (z : ℂ).im = 0 := by
      have := congrArg Complex.im h2
      simpa using this
    have hs : s = 0 := (mul_eq_zero.1 h3).resolve_right hzim.ne'
    refine ⟨hs, ?_⟩
    rw [hs] at h2
    simpa using h2
  let L : PeriodPair := ⟨(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ, hind⟩
  obtain ⟨e2, e3⟩ := g_eq L z rfl
  have hπω : (Real.pi : ℂ) * L.ω₂⁻¹ = μ := by
    show (Real.pi : ℂ) * ((Real.pi : ℂ) / μ)⁻¹ = μ
    field_simp
  refine ⟨L, ?_, ?_⟩
  · rw [e2, hπω, hμ4]
    ring
  · rw [e3, hπω, hμ6]
    ring
end GlobalTheory.DiscUniformisation
