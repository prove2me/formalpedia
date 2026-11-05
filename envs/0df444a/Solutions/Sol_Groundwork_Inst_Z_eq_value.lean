-- Prove2me | solution 1 for Groundwork.Inst.Z_eq_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:11.709679+00:00
-- url     : https://prove2.me/submissions/5a93227d-656d-4862-a4b6-8b29c2f569fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_Inst_Z_pad_eq_value
import Theorems.Thm_Groundwork_mem_tuples


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
namespace Inst
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = (R.net d).value := by
  rw [← Inst.Z_pad_eq_value R d d univ id (by simp)]
  unfold Inst.Z Inst.pad
  refine Finset.sum_congr rfl fun Λ hΛ => Finset.prod_congr rfl fun v _ => ?_
  have hv : Λ (v, v) = d := ((mem_tuples _ _ _ _).1 hΛ (v, v)).2 (by simp)
  simp only [mem_univ, implies_true, ite_true, id]
  congr 1
  funext w
  split_ifs with hw
  · subst hw; simp [star, pr, hv]
  · rfl
end Inst
end Groundwork
