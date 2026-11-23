-- Prove2me | solution 1 for GlobalTheory.ThetaInter.sum_out_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:32.464569+00:00
-- url     : https://prove2.me/submissions/3fa47a5c-1567-473e-807f-85c5f3a1ce81

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
namespace GlobalTheory.ThetaInter
theorem _root_.solution {G M : Type*} [AddCommGroup G] [AddCommMonoid M] (S : AddSubgroup G) [Fintype (G ⧸ S)]
    (f : G → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (g : G) :
    ∑ c : G ⧸ S, f (g + Quotient.out c) = ∑ c : G ⧸ S, f (Quotient.out c) := by
  refine Fintype.sum_equiv (Equiv.addLeft (g : G ⧸ S)) _ _ fun c => ?_
  have h : -(g + Quotient.out c) + Quotient.out ((g : G ⧸ S) + c) ∈ S := by
    rw [← QuotientAddGroup.eq]
    simp
  have := hf (g + Quotient.out c) _ h
  rw [add_neg_cancel_left] at this
  simpa using this.symm
end GlobalTheory.ThetaInter
