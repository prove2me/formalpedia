-- Prove2me | solution 1 for Nary.restrict_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:42.49634+00:00
-- url     : https://prove2.me/submissions/ac0555d1-f45b-46c4-9043-eb3973695967

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution : restrict (Function.const _ b) c i = (Function.const _ b) := by ext; simp
end Nary
