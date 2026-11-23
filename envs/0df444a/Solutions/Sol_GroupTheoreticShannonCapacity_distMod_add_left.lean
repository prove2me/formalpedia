-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.distMod_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:34.288849+00:00
-- url     : https://prove2.me/submissions/f7a61518-37f4-4cef-adfb-332cbee495c0

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p : ℕ) [NeZero p] (c u v : ZMod p) :
    distMod p (c + u) (c + v) = distMod p u v := by
  simp only [distMod]
  have h : (c + u) - (c + v) = u - v := by ring
  rw [h]
end GroupTheoreticShannonCapacity
