-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.IsEllipticAt.hasOrder_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:37.279617+00:00
-- url     : https://prove2.me/submissions/ca3d8612-4b95-4ea8-a276-0c12e3533c83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_smulLeft
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_comm_prinOp
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
theorem _root_.solution (h : IsEllipticAt T m x₀) (ψ : 𝓢(E, ℂ)) : HasOrder (comm T ψ) ((m : ℝ) - 1) := by
  obtain ⟨n, a, w, N, rfl, hN, -, -⟩ := h
  rw [comm_add]
  refine (hasOrder_comm_prinOp a w ψ).add ?_
  have h1 := (hN.comp (hasOrder_smulLeft ψ)).mono (le_of_eq (add_zero _))
  have h2 := ((hasOrder_smulLeft ψ).comp hN).mono (le_of_eq (zero_add _))
  exact h1.sub h2
end GroundTheory.Automorphic.Sobolev.IsEllipticAt
