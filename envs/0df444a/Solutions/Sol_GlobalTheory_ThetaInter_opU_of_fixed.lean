-- Prove2me | solution 1 for GlobalTheory.ThetaInter.opU_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.830619+00:00
-- url     : https://prove2.me/submissions/ef0f5800-e802-4586-9480-39d8760c94e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_sq

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
theorem _root_.solution {A : AddSubgroup V} (hs : IsSemiChar H A α) {F : V → ℂ} (hF : F ∈ fixedBy H α A)
    {x : V} (hx : x ∈ A) : opU H x F = fun z => α x * F z := by
  funext z
  rw [← hF x hx z, ← mul_assoc, alpha_sq hs hx, one_mul]
end GlobalTheory.ThetaInter
