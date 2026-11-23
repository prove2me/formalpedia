-- Prove2me | solution 1 for GlobalTheory.ThetaInter.out_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:32.32373+00:00
-- url     : https://prove2.me/submissions/919f311b-a9c2-44f2-8ed3-559d46feb317

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
theorem _root_.solution {A₁ A₂ : AddSubgroup V} (c : A₂ ⧸ A₁.addSubgroupOf A₂) :
    ((Quotient.out c : A₂) : V) ∈ A₁ ↔ c = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
end GlobalTheory.ThetaInter
