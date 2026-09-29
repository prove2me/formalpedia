-- Prove2me | solution 1 for InverseGalois.shrink_faithfulSMul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:35.653791+00:00
-- url     : https://prove2.me/submissions/055a85dd-1d49-4c4f-b572-b6e82e0d55cc

import Mathlib

universe u

theorem solution {G : Type u} [Fintype G] [Group G] :
    FaithfulSMul G (Shrink.{0} G) := by
  constructor
  intro g h heq
  have hh := congrArg (equivShrink.{0} G).symm
    (heq (equivShrink.{0} G (1 : G)))
  simpa only [equivShrink_symm_smul, Equiv.symm_apply_apply, smul_eq_mul, mul_one] using hh
