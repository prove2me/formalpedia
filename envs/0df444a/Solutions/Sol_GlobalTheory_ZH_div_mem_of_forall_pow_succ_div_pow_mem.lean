-- Prove2me | solution 1 for GlobalTheory.ZH.div_mem_of_forall_pow_succ_div_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:50.363806+00:00
-- url     : https://prove2.me/submissions/b7d94caa-8bf0-4e46-8c69-0b22ca009ed1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DivMemOfForallPowSuccDivPowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.ZH
namespace GlobalTheory.ZH
theorem _root_.solution :
    ∀ (Ω : Type) [Field Ω] (O : Subring Ω) [ValuationRing O] [IsNoetherianRing O],
      (∀ x : Ω, x ∈ O ∨ x⁻¹ ∈ O) → ∀ f f' : Ω, f ≠ 0 → f' ≠ 0 →
        (∀ j : ℕ, 1 ≤ j → f' ^ (j + 1) / f ^ j ∈ O) → f' / f ∈ O := by
  intro Ω _ O _ _ hO f f' hf hf' h
  by_contra hn
  have hg : f / f' ∈ O := by
    rcases hO (f' / f) with h1 | h1
    · exact absurd h1 hn
    · simpa using h1
  set g : O := ⟨f / f', hg⟩ with hgdef
  have hI : Ideal.span {g} ≠ ⊤ := by
    intro htop
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_top.mp htop).exists_right_inv
    have hu' : f / f' * (u : Ω) = 1 := congrArg Subtype.val hu
    have : (u : Ω) = f' / f := by
      field_simp at hu' ⊢
      linear_combination hu'
    exact hn (this ▸ u.2)
  have hK := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hmem : (⟨f' ^ (1 + 1) / f ^ 1, h 1 le_rfl⟩ : O) ∈ ⨅ n : ℕ, Ideal.span {g} ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨f' ^ (n + 1 + 1) / f ^ (n + 1), h (n + 1) (by omega)⟩, Subtype.ext ?_⟩
    simp only [hgdef, Subring.coe_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
    ring
  rw [hK, Ideal.mem_bot] at hmem
  have h0 : f' ^ (1 + 1) / f ^ 1 = 0 := congrArg Subtype.val hmem
  exact div_ne_zero (pow_ne_zero _ hf') (pow_ne_zero _ hf) h0
end GlobalTheory.ZH
