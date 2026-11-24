-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitRow.IdxV.relIndex_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:39:49.459656+00:00
-- url     : https://prove2.me/submissions/9965901f-279c-43f6-9568-3e5549b23544

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitRow_IdxV_mem_ball
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.SplitRow.IdxV
theorem _root_.solution (ϖ : kˣ) (hϖ : ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ) (b : ℤ) :
    (ball (1 : k)).relIndex (ball ((ϖ ^ b : kˣ) : k)) = resCard k ^ b.toNat := by
  obtain ⟨p, hp, hpϖ⟩ := hϖ
  have hne : (ϖ : k) ≠ 0 := ϖ.ne_zero
  obtain ⟨m, rfl | rfl⟩ := b.eq_nat_or_neg
  · let f : 𝒪[k] →+ k := (AddMonoidHom.mulRight (((ϖ : k) ^ m)⁻¹)).comp (𝒪[k]).subtype.toAddMonoidHom
    have hf : ∀ x, f x = (x : k) * ((ϖ : k) ^ m)⁻¹ := fun _ => rfl
    have h1 : ball ((ϖ ^ (m : ℤ) : kˣ) : k) = (⊤ : AddSubgroup 𝒪[k]).map f := by
      ext x
      simp only [mem_ball, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, hf, zpow_natCast,
        Units.val_pow_eq_pow_val]
      constructor
      · intro h
        exact ⟨⟨_, h⟩, by field_simp⟩
      · rintro ⟨y, rfl⟩
        rw [inv_mul_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    have h2 : (ball (1 : k)).comap f = ((IsLocalRing.maximalIdeal 𝒪[k]) ^ m).toAddSubgroup := by
      ext x
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp, Ideal.span_singleton_pow,
        AddSubgroup.mem_comap, mem_ball, hf, mul_one, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
      constructor
      · intro h
        refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
        push_cast
        rw [hpϖ]; field_simp
      · rintro ⟨y, rfl⟩
        push_cast
        rw [hpϖ, mul_inv_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2, Int.toNat_natCast]
    exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[k])
  · rw [Int.toNat_neg_natCast, pow_zero, AddSubgroup.relIndex_eq_one]
    intro x hx
    rw [mem_ball] at hx ⊢
    have : x * 1 = x * ((ϖ ^ (-(m : ℤ)) : kˣ) : k) * ((p ^ m : 𝒪[k]) : k) := by
      push_cast
      rw [hpϖ]
      simp only [_root_.zpow_neg, zpow_natCast]
      field_simp
    rw [this]
    exact mul_mem hx (p ^ m).2
end GlobalTheory.CompanionTheory.SplitRow.IdxV
