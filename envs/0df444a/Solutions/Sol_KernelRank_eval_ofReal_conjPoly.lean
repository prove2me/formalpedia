-- Prove2me | solution 1 for KernelRank.eval_ofReal_conjPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:53.430697+00:00
-- url     : https://prove2.me/submissions/a66e0f39-4f51-468d-9184-27e2c28ac0b5

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (A : ℂ[X]) (u : ℝ) :
    (conjPoly A).eval (u : ℂ) = starRingEnd ℂ (A.eval (u : ℂ)) := by
  rw [conjPoly, eval_map, ← eval₂_id, hom_eval₂, RingHom.comp_id, Complex.conj_ofReal]
end KernelRank
