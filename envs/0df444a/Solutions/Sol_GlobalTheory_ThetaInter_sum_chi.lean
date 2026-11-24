-- Prove2me | solution 1 for GlobalTheory.ThetaInter.sum_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:43:32.614461+00:00
-- url     : https://prove2.me/submissions/04c8bc7a-48fc-4747-944a-3f85fffc4c30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_sum_out_shift
import Theorems.Thm_GlobalTheory_ThetaInter_chi_add_left
import Theorems.Thm_GlobalTheory_ThetaInter_chi_eq_one_iff
import Theorems.Thm_GlobalTheory_ThetaInter_int_swap

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
open Classical
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Fintype (A₁ ⧸ A₂.addSubgroupOf A₁)]
    (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂) {y : V} (hy : y ∈ A₂) :
    ∑ c : A₁ ⧸ A₂.addSubgroupOf A₁, chi H ((Quotient.out c : A₁) : V) y =
      if y ∈ A₁ then (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) : ℂ) else 0 := by
  split_ifs with h
  · have : ∀ c : A₁, chi H (c : V) y = 1 := fun c => (chi_eq_one_iff _ y).2 ((hd₁.ge c.2) y h)
    simp [this]
  · obtain ⟨p, hp, hp'⟩ : ∃ p ∈ A₁, chi H p y ≠ 1 := by
      by_contra hc
      push Not at hc
      exact h (hd₁.le fun p hp => int_swap hH ((chi_eq_one_iff _ _).1 (hc p hp)))
    have := sum_out_shift (A₂.addSubgroupOf A₁) (fun a : A₁ => chi H (a : V) y) (fun a s hs => by
      rw [AddSubgroup.coe_add, chi_add_left, (chi_eq_one_iff _ y).2 ((hd₂.ge (AddSubgroup.mem_addSubgroupOf.1 hs)) y hy), mul_one]) ⟨p, hp⟩
    simp only [AddSubgroup.coe_add, chi_add_left, ← Finset.mul_sum] at this
    have h2 := sub_eq_zero.2 this
    rw [← sub_one_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hp')
end GlobalTheory.ThetaInter
