-- Prove2me | solution 1 for GlobalTheory.ClosingLemmaSecond.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:18.797817+00:00
-- url     : https://prove2.me/submissions/f96ef720-75be-4891-a8cb-77a905f37aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosingLemmaSecond
namespace GlobalTheory.ClosingLemmaSecond
theorem _root_.solution : ∀ {R : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R}, q ≠ (0 : R) → ∃ (c : ℕ), ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by
  intro R _ _ _ I q hq
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {q} : Submodule R R)
  refine ⟨k, fun n a ha => ?_⟩
  have hmem : q * a ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {q} := by
    refine Submodule.mem_inf.2 ⟨?_, Ideal.mem_span_singleton.2 ⟨a, rfl⟩⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hk (n + k) (by omega), Nat.add_sub_cancel] at hmem
  have hle : I ^ n • (I ^ k • (⊤ : Submodule R R) ⊓ Ideal.span {q}) ≤ I ^ n • Ideal.span {q} :=
    Submodule.smul_le.2 fun r hr x hx => Submodule.smul_mem_smul hr (Submodule.mem_inf.1 hx).2
  have h2 := hle hmem
  rw [Ideal.smul_eq_mul, mul_comm, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨z, hz, hzq⟩ := h2
  rwa [← mul_left_cancel₀ hq hzq]
end GlobalTheory.ClosingLemmaSecond
