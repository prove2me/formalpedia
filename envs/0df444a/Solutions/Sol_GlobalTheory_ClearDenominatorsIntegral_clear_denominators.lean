-- Prove2me | solution 1 for GlobalTheory.ClearDenominatorsIntegral.clear_denominators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:27.298812+00:00
-- url     : https://prove2.me/submissions/5202ae78-b964-4a45-9878-72bb67d34f50

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ClearDenominators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClearDenominatorsIntegral
open GlobalTheory.UnitLemma
namespace GlobalTheory.ClearDenominatorsIntegral
theorem _root_.solution (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h
end GlobalTheory.ClearDenominatorsIntegral
