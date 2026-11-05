-- Prove2me | solution 1 for Groundwork.prod_le_prod_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:54.348654+00:00
-- url     : https://prove2.me/submissions/380b39fc-3363-4f8b-a4d6-edbdc4586bb1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
theorem _root_.solution {ι R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] (s : Finset ι)
    (f g : ι → R) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.prod_cons, Finset.forall_mem_cons] at *
    exact mul_le_mul h1.1 (ih h0.2 h1.2) (Finset.prod_nonneg h0.2) (h0.1.trans h1.1)
end Groundwork
