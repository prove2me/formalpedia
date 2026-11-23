-- Prove2me | solution 1 for KernelRank.Component.eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:47:47.074287+00:00
-- url     : https://prove2.me/submissions/87320396-6abf-4813-8411-77866ced8a77

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
namespace Component
theorem _root_.solution (c : Component) (s : ℝ) : c.eval s = (expPoly c.poly c.rate s).re := rfl
end Component
end KernelRank
