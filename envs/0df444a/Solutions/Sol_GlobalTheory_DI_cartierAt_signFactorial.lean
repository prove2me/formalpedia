-- Prove2me | solution 1 for GlobalTheory.DI.cartierAt_signFactorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:56.656208+00:00
-- url     : https://prove2.me/submissions/7c4a29fd-2032-426e-8f62-7ce0e57cfcb0

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScaling
import Theorems.Thm_GlobalTheory_DI_exists_inv_signFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E)
    (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) →
    (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  intro E _ p hp d γ γ' N T hE hN hγ hC
  have hp0 : 0 < p := hp.out.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [hγ 0 x hx] at h0
    simp at h0
    exact hC.inj_zero x hx h0
  · intro a x hx z hz h
    by_cases hpa : p ≤ a + 1
    · rw [hN _ hpa] at hx; exact (AddSubgroup.mem_bot.1 hx)
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      apply hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)
      rw [hγ _ x hx] at h
      rw [map_zsmul, ← h, ← mul_smul, hu]
  · intro y hy hd
    obtain ⟨x, hx, rfl⟩ := hC.surj_zero y hy hd
    exact ⟨x, hx, by rw [hγ 0 x hx]; simp⟩
  · intro a y hy hd
    obtain ⟨x, hx, z, hz, rfl⟩ := hC.surj_succ a y hy hd
    by_cases hpa : p ≤ a + 1
    · have hx0 : x = 0 := by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx
      subst hx0
      refine ⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩
      rw [hγ (a + 1) 0 (AddSubgroup.zero_mem _)]; simp
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      refine ⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩
      rw [hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]
end GlobalTheory.DI
