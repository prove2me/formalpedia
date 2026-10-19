-- Prove2me | solution 1 for MazurTransfer.Order13ReflectionParameter.exists_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:06:59.452978+00:00
-- url     : https://prove2.me/submissions/0521b11d-394a-4514-89b2-3d1a52fa1b0b

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal coefficients for an order-13 reflection, together
with transcendence of its fractional-linear coordinate. Named downstream
consumer: the actual scheme function-field reflection automorphism.
-/

noncomputable section
universe u v
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter Polynomial

theorem solution {K : Type u} [Field K] [IsAlgClosed K] : Nonempty (ReflectionParameter K) := by
  let p : Polynomial K := X ^ 3 + C 4 * X ^ 2 + X - C 1
  have hp : p.degree ≠ 0 := by
    have hd : p.degree = 3 := by
      dsimp [p]
      compute_degree!
    rw [hd]
    decide
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p hp
  have ht' : reflectionCubic t = 0 := by
    simpa only [Polynomial.IsRoot, p, eval_sub, eval_add, eval_mul, eval_pow,
      eval_X, eval_C, reflectionCubic] using ht
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (reflectionScalar t) (by decide : 0 < 2)
  exact ⟨⟨t, s, ht', hs⟩⟩

#print axioms solution
