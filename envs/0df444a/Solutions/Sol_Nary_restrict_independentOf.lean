-- Prove2me | solution 1 for Nary.restrict_independentOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:33.608146+00:00
-- url     : https://prove2.me/submissions/b290b4d8-9569-4739-bc65-522fc07c4910

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution : IndependentOf (restrict f c i) i := by simp
end Nary
