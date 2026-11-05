-- Prove2me | solution 1 for Groundwork.Inst.toInst_net
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:12.330302+00:00
-- url     : https://prove2.me/submissions/6f455ee3-9953-46bb-b095-a26336ee7951

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_mem_tuples


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
namespace Inst
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [DecidableEq A'] (R : Inst J A) (d : A)
    (D : Finset A') (dec : A' → A) : (R.net d).toInst (fun _ _ => D) (fun _ _ => dec) = R.pad d D dec := by
  funext v θ
  unfold Network.toInst Inst.pad Inst.net
  simp only
  split_ifs with hall
  · rw [Finset.sum_eq_single (fun w => if w = v then d else dec (θ w))]
    · rw [Finset.prod_eq_one, mul_one]
      intro b hb
      have hb' : b ≠ v := by simpa using hb
      simp [hall b hb', hb']
    · intro z hz hne
      have hz' := (mem_tuples _ _ _ _).1 hz
      obtain ⟨b, hb⟩ : ∃ b, z b ≠ (if b = v then d else dec (θ b)) := by
        by_contra hcon
        exact hne (funext fun b => by_contra fun hb => hcon ⟨b, hb⟩)
      have hbv : b ≠ v := by
        rintro rfl
        exact hb (by simpa using (hz' b).2 (by simp))
      rw [Finset.prod_eq_zero (i := b) (by simp [hbv]), mul_zero]
      simp only [hbv, ite_false] at hb
      simp [hall b hbv, hb]
    · intro hn
      exact absurd ((mem_tuples _ _ _ _).2 fun w => ⟨fun _ => mem_univ _, fun hw => by simp at hw; simp [hw]⟩) hn
  · obtain ⟨w, hw, hwD⟩ : ∃ w, w ≠ v ∧ θ w ∉ D := by
      by_contra hcon
      exact hall fun w hw => by_contra fun hD => hcon ⟨w, hw, hD⟩
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [Finset.prod_eq_zero (i := w) (by simp [hw]), mul_zero]
    simp [hwD]
end Inst
end Groundwork
