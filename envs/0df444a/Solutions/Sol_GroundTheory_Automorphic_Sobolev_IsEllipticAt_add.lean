-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.IsEllipticAt.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:20.93899+00:00
-- url     : https://prove2.me/submissions/86e2139e-5d87-4f74-bdf0-541752b6eea6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_add
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.IsEllipticAt
variable {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
namespace GroundTheory.Automorphic.Sobolev.IsEllipticAt
theorem _root_.solution (h : IsEllipticAt T m x₀) {N' : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (hN' : HasOrder N' ((m : ℝ) - 1)) (hL : IsLocal N') : IsEllipticAt (T + N') m x₀ := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, hell⟩ := h
  exact ⟨n, a, w, N + N', by rw [add_assoc], hN.add hN', hNl.add hL, hell⟩
end GroundTheory.Automorphic.Sobolev.IsEllipticAt
