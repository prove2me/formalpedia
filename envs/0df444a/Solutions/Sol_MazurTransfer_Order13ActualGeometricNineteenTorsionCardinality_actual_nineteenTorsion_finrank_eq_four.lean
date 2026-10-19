-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_finrank_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T10:34:04.908928+00:00
-- url     : https://prove2.me/submissions/6bc0bd78-32c4-4c4c-9663-fc9d1b39acd9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original F19-module on the SAME actual Picard
nineteen-torsion carrier has dimension four, using its cardinality.
Named downstream consumer: actual norm-kernel dimension sum and ranks.
-/
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionOriginalZModModuleData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_nineteenTorsion_card_eq_pow_four
noncomputable section
open MazurTransfer
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionCardinality
local instance nineteenTorsionFinrankOriginalPrimeProvider20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
attribute [local instance] nineteenTorsionZModModule
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

theorem solution : Module.finrank (ZMod 19) (NineteenTorsion K) = 4 := by
  letI : Finite (NineteenTorsion K) := nineteenTorsion_finite K
  have h := Module.natCard_eq_pow_finrank (K := ZMod 19) (V := NineteenTorsion K)
  rw [Nat.card_zmod, actual_nineteenTorsion_card_eq_pow_four K] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 19) h.symm

#print axioms solution
