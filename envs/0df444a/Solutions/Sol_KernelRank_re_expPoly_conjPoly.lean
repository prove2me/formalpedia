-- Prove2me | solution 1 for KernelRank.re_expPoly_conjPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:15.446984+00:00
-- url     : https://prove2.me/submissions/6f066770-2ca6-4ca9-84da-85d0a093d00c

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
import Theorems.Thm_KernelRank_conj_expPoly


set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (A : ℂ[X]) (ν : ℂ) (u : ℝ) :
    (expPoly (conjPoly A) (starRingEnd ℂ ν) u).re = (expPoly A ν u).re := by
  rw [← conj_expPoly, Complex.conj_re]
end KernelRank
