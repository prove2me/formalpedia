-- Prove2me | solution 1 for N25.GammaH25_factorization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:14.382096+00:00
-- url     : https://prove2.me/submissions/d3c81499-c4be-4fbe-a072-b1f0c0985380

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

open CongruenceSubgroup

namespace N25

/-- The lower-right residue character identifies the quotient by Gamma1. -/
theorem _root_.solution (T : Gamma0 25)
    (hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 7 (by decide))⁻¹)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CohCarrier.GammaH 25 N25.H25) :
    ∃ n : ℤ, A * (T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ n ∈ Gamma1 25 := by
  obtain ⟨B, hB, rfl⟩ := hA
  change CohCarrier.gamma0Units 25 B ∈ Subgroup.zpowers (ZMod.unitOfCoprime 7 (by decide)) at hB
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hB
  have hunit : CohCarrier.gamma0Units 25 (B * T ^ n) = 1 := by
    rw [map_mul, map_zpow, hT, ← hn, inv_zpow, mul_inv_cancel]
  have hker : B * T ^ n ∈ Gamma1' 25 := by
    rw [Gamma1_mem']
    exact congrArg Units.val hunit
  refine ⟨n, ?_⟩
  rw [Gamma1_mem]
  simpa using (Gamma1_to_Gamma0_mem (B * T ^ n)).mp hker

end N25
