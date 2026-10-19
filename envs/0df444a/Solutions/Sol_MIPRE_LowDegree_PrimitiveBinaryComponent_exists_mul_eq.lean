-- Prove2me | solution 1 for MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:49.361013+00:00
-- url     : https://prove2.me/submissions/3c1ecd4b-c8a3-4d69-bd11-f83f86c5069b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean (solution of MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Theorems.Thm_MIPRE_LowDegree_exists_pow_succ_eq_self_of_square_bijective

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.PrimitiveBinaryComponent
variable {R : Type*} [CommRing R] [Finite R]
theorem _root_.solution
    (hsq : Function.Bijective (fun x : R => x * x)) {e : R}
    (he : PrimitiveBinaryComponent e) (x : R) (hx : x ≠ 0) (hex : e * x = x) :
    ∃ y : R, x * y = e := by
  obtain ⟨n, hn, hp⟩ := exists_pow_succ_eq_self_of_square_bijective hsq x
  have hid : x ^ n * x ^ n = x ^ n := by
    have h : x ^ (n + n) = x ^ n := by
      calc
        x ^ (n + n) = x ^ (n + 1) * x ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ = x * x ^ (n - 1) := by rw [hp]
        _ = x ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
    simpa only [pow_add] using h
  have hne : x ^ n ≠ 0 := by
    intro hz
    rw [pow_succ, hz, zero_mul] at hp
    exact hx hp.symm
  have hepow : e * x ^ n = x ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ']
    calc
      e * (x * x ^ m) = (e * x) * x ^ m := (mul_assoc ..).symm
      _ = x * x ^ m := by rw [hex]
  have hu : x ^ n = e := by
    rcases he.2.2 (x ^ n) hid with h | h
    · exact (hne (hepow.symm.trans h)).elim
    · exact hepow.symm.trans h
  refine ⟨x ^ (n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel hn, hu]
end MIPRE.LowDegree.PrimitiveBinaryComponent
