-- Prove2me | solution 1 for GlobalTheory.ThetaInter.alpha_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:54.948941+00:00
-- url     : https://prove2.me/submissions/74ae5270-cda0-4c91-8c07-b017fd3ecfed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

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
variable {α : V → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : α x * α x = 1 := by
  rcases hs.1 x hx with h | h <;> simp [h]
end GlobalTheory.ThetaInter
