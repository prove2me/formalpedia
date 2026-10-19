-- Prove2me | solution 1 for MIPRE.LowDegree.add_self_injective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:08.984791+00:00
-- url     : https://prove2.me/submissions/121549a2-80ae-46f7-a2b1-89f7006206d0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (solution of MIPRE.LowDegree.add_self_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
theorem _root_.solution (hG : Odd (Fintype.card G)) :
    Function.Injective fun g : G => g + g := by
  intro a b hab
  simp only at hab
  have h2 : (a - b) + (a - b) = 0 := by
    have e : (a - b) + (a - b) = (a + a) - (b + b) := by abel
    rw [e, hab, sub_self]
  have hord : addOrderOf (a - b) ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul]; exact h2)
  have hcard : addOrderOf (a - b) ∣ Fintype.card G := addOrderOf_dvd_card
  have hcop : Nat.Coprime 2 (Fintype.card G) := Nat.coprime_two_left.mpr hG
  have hdvd : addOrderOf (a - b) ∣ 1 := hcop ▸ Nat.dvd_gcd hord hcard
  exact sub_eq_zero.mp (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
end MIPRE.LowDegree
