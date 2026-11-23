-- Prove2me | solution 1 for Mdp.DiscountedMDP.value_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:32:25.511546+00:00
-- url     : https://prove2.me/submissions/985e6099-5bf4-4021-ab9a-9eb4af6c125c

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (d : S → A) : M.Lpolicy d (M.value d) = M.value d :=
  (M.contractingWith_Lpolicy d).fixedPoint_isFixedPt
end Mdp.DiscountedMDP
