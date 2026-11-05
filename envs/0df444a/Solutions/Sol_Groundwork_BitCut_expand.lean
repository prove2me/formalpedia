-- Prove2me | solution 1 for Groundwork.BitCut.expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:03.794894+00:00
-- url     : https://prove2.me/submissions/68ad9333-b020-4a14-9c16-a0a9e699fa05

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
import Theorems.Thm_Groundwork_prod_mul_prod_compl_eq_ite

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
namespace BitCut
theorem _root_.solution (c : BitCut) (D0 D1 : Bool → Bool → Bool → Bool → ℤ)
    (h0 : ∀ a b c' d, D0 a b c' d = ∑ h, c.top h a b * c.bot0 h c' d)
    (h1 : ∀ a b c' d, D1 a b c' d = ∑ h, c.top h a b * c.bot1 h c' d) {n : ℕ} (i : ℕ) (a b c' d : Bits n) :
    ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
        (∏ k ∈ S, D1 (a k) (b k) (c' k) (d k)) * ∏ k ∈ Sᶜ, D0 (a k) (b k) (c' k) (d k)
      = ∑ β : Fin n → Bell, c.Top β a b * c.Bot i β c' d := by
  simp only [BitCut.Top, BitCut.Bot, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  have h : ∀ k, (if k ∈ S then D1 (a k) (b k) (c' k) (d k) else D0 (a k) (b k) (c' k) (d k))
      = ∑ h, c.top h (a k) (b k) * (if k ∈ S then c.bot1 h (c' k) (d k) else c.bot0 h (c' k) (d k)) := by
    intro k
    split_ifs
    · exact h1 _ _ _ _
    · exact h0 _ _ _ _
  simp only [prod_mul_prod_compl_eq_ite, ← prod_mul_distrib]
  simp_rw [h]
  rw [prod_univ_sum, Fintype.piFinset_univ]
end BitCut
end Groundwork
