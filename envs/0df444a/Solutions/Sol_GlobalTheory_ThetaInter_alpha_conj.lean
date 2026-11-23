-- Prove2me | solution 1 for GlobalTheory.ThetaInter.alpha_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:56.686272+00:00
-- url     : https://prove2.me/submissions/eae61655-0bf6-4d9d-ab64-d921d9861d95

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
theorem _root_.solution {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : conj (α x) = α x := by
  rcases hs.1 x hx with h | h <;> simp [h]
end GlobalTheory.ThetaInter
