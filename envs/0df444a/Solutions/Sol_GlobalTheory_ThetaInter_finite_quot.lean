-- Prove2me | solution 1 for GlobalTheory.ThetaInter.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:32.807822+00:00
-- url     : https://prove2.me/submissions/e73d8b3d-9f17-44bc-ae46-2a8a566ced06

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
omit [Module ℂ V]
namespace GlobalTheory.ThetaInter
theorem _root_.solution {A₁ A₂ : AddSubgroup V} (hfg : A₂.FG) (h : ∀ x ∈ A₂, ∃ m : ℕ, 0 < m ∧ m • x ∈ A₁) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := by
  have : AddGroup.FG A₂ := (AddGroup.fg_iff_addSubgroup_fg A₂).2 hfg
  refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨m, hm, hx⟩ := h x x.2
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hx
end GlobalTheory.ThetaInter
