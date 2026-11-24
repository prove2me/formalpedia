-- Prove2me | solution 1 for GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:49.683266+00:00
-- url     : https://prove2.me/submissions/6b50d9e2-a228-4bcc-b2e5-6712c01f5adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroScalarMembership
namespace GlobalTheory.NonzeroScalarMembership
theorem _root_.solution {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay
end GlobalTheory.NonzeroScalarMembership
