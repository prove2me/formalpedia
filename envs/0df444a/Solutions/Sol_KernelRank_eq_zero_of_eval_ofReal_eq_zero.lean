-- Prove2me | solution 1 for KernelRank.eq_zero_of_eval_ofReal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:36.483042+00:00
-- url     : https://prove2.me/submissions/bcecf91e-17fc-4dc1-85e4-2fdde8ae7d52

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {P : ℂ[X]} (h : ∀ u : ℝ, 0 < u → P.eval (u : ℂ) = 0) :
    P = 0 := by
  refine eq_zero_of_infinite_isRoot P ?_
  refine Set.Infinite.mono ?_ ((Set.Ioi_infinite (0 : ℝ)).image ofReal_injective.injOn)
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu
end KernelRank
