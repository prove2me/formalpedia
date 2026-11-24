-- Prove2me | solution 1 for GlobalTheory.ThetaInter.inter_mem_fixedBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:30.149803+00:00
-- url     : https://prove2.me/submissions/4dea415d-4cef-481c-8796-5a239610ec28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_sum_out_shift
import Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
import Theorems.Thm_GlobalTheory_ThetaInter_opU_sum
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_sq
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_opU_add
import Theorems.Thm_GlobalTheory_ThetaInter_opU_of_fixed
import Theorems.Thm_GlobalTheory_ThetaInter_inter_eq

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
theorem _root_.solution (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) : inter H α A₁ A₂ F ∈ fixedBy H α A₂ := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  intro y hy z
  rw [inter_eq, opU_mul, opU_sum, mul_left_comm, Finset.mul_sum]
  congr 1
  rw [← sum_out_shift (A₁.addSubgroupOf A₂) (fun a : A₂ => α (a : V) * opU H (a : V) F z) ?_ ⟨y, hy⟩]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [opU_mul, AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ hy (Quotient.out c).2]
  · intro a s hs
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 s.2, opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 hs), opU_mul,
      ← mul_assoc (α s), alpha_sq hs₂ s.2, one_mul]
end GlobalTheory.ThetaInter
