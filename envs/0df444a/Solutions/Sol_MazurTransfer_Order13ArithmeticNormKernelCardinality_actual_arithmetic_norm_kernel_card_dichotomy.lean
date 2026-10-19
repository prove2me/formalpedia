-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:10:28.188383+00:00
-- url     : https://prove2.me/submissions/8e1e67f3-3dd8-4b4f-8133-0af00d8e795f

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_product
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the original MazurTheorem arithmetic norm-kernel computation and official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the two actual arithmetic norm-kernel cardinalities are one and nineteen in some order. Named downstream consumer: rational Picard norm-kernel ordering and the Galois fixed-part computation.
-/
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem solution :
    (Nat.card pi.ker = 19 ∧ Nat.card piConjugate.ker = 1) ∨
      (Nat.card pi.ker = 1 ∧ Nat.card piConjugate.ker = 19) := by
  obtain ⟨_, _, h⟩ := MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product
  have hp : Nat.Prime 19 := by decide
  have hd : Nat.card pi.ker ∣ 19 := ⟨Nat.card piConjugate.ker, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h19
  · exact Or.inr ⟨h1, by simpa only [h1, one_mul] using h⟩
  · apply Or.inl
    refine ⟨h19, ?_⟩
    rw [h19] at h
    omega
#print axioms solution
