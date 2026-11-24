-- Prove2me | solution 1 for GlobalTheory.ThetaInter.span_inf_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.862252+00:00
-- url     : https://prove2.me/submissions/6d4edeb9-abb8-4e68-af43-24db41cdafaa

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
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hsp : Submodule.span ℝ (A₂ : Set W) = ⊤) : Submodule.span ℝ ((A₁ ⊓ A₂ : AddSubgroup W) : Set W) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  intro x hx
  have h0 : (A₁.addSubgroupOf A₂).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have h1 := AddSubgroup.mem_addSubgroupOf.1 ((A₁.addSubgroupOf A₂).nsmul_index_mem ⟨x, hx⟩)
  have h2 : (A₁.addSubgroupOf A₂).index • x ∈ A₁ ⊓ A₂ := ⟨h1, A₂.nsmul_mem hx _⟩
  have h3 := Submodule.smul_mem _ (((A₁.addSubgroupOf A₂).index : ℝ)⁻¹) (Submodule.subset_span (R := ℝ) h2)
  rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h0), one_smul] at h3
end GlobalTheory.ThetaInter
