-- Prove2me | solution 1 for GlobalTheory.ThetaInter.inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:30.541072+00:00
-- url     : https://prove2.me/submissions/b977ce25-89d6-49a0-80f0-002e3d94f9e2

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
theorem _root_.solution (A₁ A₂ : AddSubgroup V) [Fintype (A₂ ⧸ A₁.addSubgroupOf A₂)] (F : V → ℂ) :
    inter H α A₁ A₂ F = fun z => ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂,
        α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z := by
  funext z
  rw [inter, finsum_eq_sum_of_fintype, relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
end GlobalTheory.ThetaInter
