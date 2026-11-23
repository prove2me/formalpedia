-- Prove2me | solution 1 for GlobalTheory.ThetaInter.int_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:07.760836+00:00
-- url     : https://prove2.me/submissions/ba839a98-8bd8-448d-89f5-a9e0b8ca3fcc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_altE_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {x y : V} (h : ∃ m : ℤ, altE H x y = m) : ∃ m : ℤ, altE H y x = m := by
  obtain ⟨m, hm⟩ := h
  exact ⟨-m, by rw [altE_swap hH, hm]; simp⟩
end GlobalTheory.ThetaInter
