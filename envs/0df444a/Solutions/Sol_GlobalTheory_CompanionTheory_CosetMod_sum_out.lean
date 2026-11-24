-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetMod.sum_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:40.276893+00:00
-- url     : https://prove2.me/submissions/6c3765d8-db89-43c0-91fd-55ef02508f12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetMod
namespace GlobalTheory.CompanionTheory.CosetMod
theorem _root_.solution {G : Type} [AddCommGroup G] (H : AddSubgroup G) [Fintype (G ⧸ H)] (χ : AddChar G ℂ)
    (hχ : ∀ h ∈ H, χ h = 1) :
    ((∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = Fintype.card (G ⧸ H)) ∧
      (¬ (∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = 0) := by
  have hcoset : ∀ a b : G, (a : G ⧸ H) = b → χ a = χ b := by
    intro a b hab
    have hmem : -a + b ∈ H := QuotientAddGroup.eq.mp hab
    calc χ a = χ a * χ (-a + b) := by rw [hχ _ hmem, mul_one]
      _ = χ b := by rw [← AddChar.map_add_eq_mul, add_neg_cancel_left]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [h]
  · push_neg at h
    obtain ⟨g, hg⟩ := h
    have hshift : ∀ q : G ⧸ H, χ g * χ q.out = χ ((QuotientAddGroup.mk g + q).out) := by
      intro q
      rw [← AddChar.map_add_eq_mul]
      apply hcoset
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    have key : χ g * ∑ q : G ⧸ H, χ q.out = ∑ q : G ⧸ H, χ q.out := by
      rw [Finset.mul_sum]
      simp_rw [hshift]
      exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk g)) _ _ (fun q => rfl)
    have h0 : (χ g - 1) * ∑ q : G ⧸ H, χ q.out = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hg
    · exact h1
end GlobalTheory.CompanionTheory.CosetMod
