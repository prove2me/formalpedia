-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.expand_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:10.303301+00:00
-- url     : https://prove2.me/submissions/f76ff2e3-e2c9-4856-8bad-a9eef250c6d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_dslope
import Theorems.Thm_GlobalTheory_ExplicitRect_eq_add_dslope
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {φ h : ℂ → ℂ} {m : ℂ} {u : ℝ} (hu : 0 < u)
    (hh : AnalyticAt ℂ h 0) (hφ : ∀ᶠ s in 𝓝[≠] (0 : ℂ), φ s = m / s + h s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(φ s) * (u : ℂ) ^ s / s =
        a / (s - 0) ^ 2 + (-(m * (Real.log u : ℂ) + h 0)) / (s - 0) + G s := by
  have hE : AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) 0 := analyticAt_cpow hu 0
  have hD1 := analyticAt_dslope hE
  have hD2 := analyticAt_dslope hD1
  have hDh := analyticAt_dslope hh
  have hD10 : dslope (fun s : ℂ => (u : ℂ) ^ s) 0 0 = (Real.log u : ℂ) := by
    rw [dslope_same]
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    rw [(hasStrictDerivAt_const_cpow (x := (u : ℂ)) (y := 0) (.inl hu0)).hasDerivAt.deriv,
      Complex.cpow_zero, one_mul, Complex.ofReal_log hu.le]
  refine ⟨-m, fun s => -(m * dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s + dslope h 0 s +
      h s * (Real.log u : ℂ) + h s * s * dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s),
    ((((analyticAt_const.mul hD2).add hDh).add (hh.mul analyticAt_const)).add
      ((hh.mul analyticAt_id).mul hD2)).neg, ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hs0
  have hs0' : s ≠ 0 := hs0
  have e1 := eq_add_dslope (fun s : ℂ => (u : ℂ) ^ s) 0 s
  have e2 := eq_add_dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s
  have eh := eq_add_dslope h 0 s
  simp only [Complex.cpow_zero, sub_zero] at e1 e2 eh
  rw [hD10] at e2
  rw [hs, e1, e2]
  simp only [sub_zero]
  rw [eh]
  field_simp
  ring
end GlobalTheory.ExplicitRect
