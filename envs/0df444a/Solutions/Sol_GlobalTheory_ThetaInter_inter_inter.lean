-- Prove2me | solution 1 for GlobalTheory.ThetaInter.inter_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:30.945954+00:00
-- url     : https://prove2.me/submissions/690f386b-0fe6-49f3-b6b8-e1b8b807f7d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_opU_comm
import Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
import Theorems.Thm_GlobalTheory_ThetaInter_opU_sum
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_sq
import Theorems.Thm_GlobalTheory_ThetaInter_opU_of_fixed
import Theorems.Thm_GlobalTheory_ThetaInter_inter_eq
import Theorems.Thm_GlobalTheory_ThetaInter_sum_chi
import Theorems.Thm_GlobalTheory_ThetaInter_out_mem_iff
import Theorems.Thm_GlobalTheory_ThetaInter_card_eq_card

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
theorem _root_.solution (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₁ ⧸ A₂.addSubgroupOf A₁)]
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂)
    (hs₁ : IsSemiChar H A₁ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) :
    inter H α A₂ A₁ (inter H α A₁ A₂ F) = F := by
  classical
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have := Fintype.ofFinite (A₁ ⧸ A₂.addSubgroupOf A₁)
  rw [inter_eq A₂ A₁, inter_eq A₁ A₂]
  funext z
  have key : ∀ (p : A₁) (q : V), α p * opU H p (fun w => α q * opU H q F w) z =
      chi H p q * (α q * opU H q F z) := by
    intro p q
    rw [opU_mul, opU_comm hH, opU_of_fixed hs₁ hF p.2, opU_mul]
    linear_combination (α q * chi H p q * opU H q F z) * alpha_sq hs₁ p.2
  have e : ∀ p : A₁, α p * opU H p (fun z => ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂,
        α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z) z =
      ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂, chi H p ((Quotient.out c : A₂) : V) *
        (α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z) := by
    intro p
    rw [opU_mul, opU_sum, mul_left_comm, Finset.mul_sum]
    simp only [key]
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul,
    fun d : A₂ ⧸ A₁.addSubgroupOf A₂ => sum_chi hH hd₁ hd₂ (Quotient.out d : A₂).2, out_mem_iff]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) fun b _ hb => by simp [hb], if_pos rfl,
    hF _ ((out_mem_iff _).2 rfl), ← card_eq_card hH hd₁ hd₂]
  have hpos : (0 : ℝ) < Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) := by exact_mod_cast Fintype.card_pos
  have h1 : ((Real.sqrt (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have h2 : ((Real.sqrt (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁)) : ℝ) : ℂ) ^ 2 =
      Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) := by
    exact_mod_cast Real.sq_sqrt hpos.le
  rw [← h2]
  field_simp
end GlobalTheory.ThetaInter
