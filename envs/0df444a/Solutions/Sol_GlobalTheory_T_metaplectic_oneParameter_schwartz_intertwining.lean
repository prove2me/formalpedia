-- Prove2me | solution 1 for GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:23:22.400804+00:00
-- url     : https://prove2.me/submissions/180a68cf-1f17-41a9-b7d3-58d169c47ae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwining
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwiningStatement
import Theorems.Thm_GlobalTheory_RealWeil_metaplectic_oneParam_schwartz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧ (∀ f, U 0 f = f) ∧ (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧ (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  first | exact @GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | exact GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | (intros; apply GlobalTheory.RealWeil.metaplectic_oneParam_schwartz <;> assumption)
end _root_.GlobalTheory.T
