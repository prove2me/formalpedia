-- Prove2me | solution 1 for GlobalTheory.conj_mem_zpowers_of_mem_of_pRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:49.992549+00:00
-- url     : https://prove2.me/submissions/6c370187-ca52-47f3-be13-7cea5e3d2485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
  obtain ⟨k, hk⟩ := hp _ hg
  have ho : orderOf (g⁻¹ * c * g) = orderOf c := by
    have := (MulAut.conj g⁻¹).orderOf_eq c
    simpa using this
  have hcop : Nat.Coprime (p ^ k) (orderOf (g⁻¹ * c * g)) := by
    rw [ho]
    exact Nat.Coprime.pow_left k hc.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m
end GlobalTheory
