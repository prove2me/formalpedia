-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.IsEllipticAt.isLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:39.936257+00:00
-- url     : https://prove2.me/submissions/dd65b02e-9742-4872-9585-a2c3979b8b3b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_prinOp
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
theorem _root_.solution (h : IsEllipticAt T m x₀) : IsLocal T := by
  obtain ⟨n, a, w, N, rfl, -, hN, -⟩ := h
  exact (isLocal_prinOp a w).add hN
end GroundTheory.Automorphic.Sobolev.IsEllipticAt
