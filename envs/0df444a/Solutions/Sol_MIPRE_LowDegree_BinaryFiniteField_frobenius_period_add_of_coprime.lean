-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:10.72859+00:00
-- url     : https://prove2.me/submissions/e0e05c39-8658-4af5-99f1-860effdabcc1

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (solution of MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem _root_.solution (x y : R) (a b n : ℕ) (hab : a.Coprime b)
    (hx : iterateFrobenius R 2 a x = x) (hy : iterateFrobenius R 2 b y = y)
    (hs : iterateFrobenius R 2 n (x + y) = x + y) :
    iterateFrobenius R 2 n x = x ∧ iterateFrobenius R 2 n y = y := by
  let d := iterateFrobenius R 2 n x - x
  have hd : d = y - iterateFrobenius R 2 n y := by
    rw [map_add] at hs
    dsimp [d]
    linear_combination hs
  have hda : iterateFrobenius R 2 a d = d := by
    dsimp [d]
    rw [map_sub, frobenius_comm a n, hx]
  have hdb : iterateFrobenius R 2 b d = d := by
    rw [hd, map_sub, frobenius_comm b n, hy]
  have hpa : Function.IsPeriodicPt (frobenius R 2) a d := by
    change (frobenius R 2)^[a] d = d
    rw [iterate_frobenius]
    exact hda
  have hpb : Function.IsPeriodicPt (frobenius R 2) b d := by
    change (frobenius R 2)^[b] d = d
    rw [iterate_frobenius]
    exact hdb
  have hfix : Function.IsFixedPt (frobenius R 2) d := by
    have h := hpa.gcd hpb
    rw [hab.gcd_eq_one] at h
    simpa only [Function.IsPeriodicPt, Function.iterate_one] using h
  have hdn : iterateFrobenius R 2 n d = d := by
    rw [coe_iterateFrobenius]
    exact hfix.iterate n
  have hnx : (iterateFrobenius R 2 n)^[a] x = x := by
    rw [← iterateFrobenius_mul_apply, Nat.mul_comm n a, iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hx n
  have hny : (iterateFrobenius R 2 n)^[b] y = y := by
    rw [← iterateFrobenius_mul_apply, Nat.mul_comm n b, iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hy n
  have hax : a • d = 0 := nsmul_delta_eq_zero (iterateFrobenius R 2 n).toAddMonoidHom x a hdn hnx
  have hby : b • d = 0 := by
    have he : iterateFrobenius R 2 n y - y = -d := by rw [hd]; abel
    have hz := nsmul_delta_eq_zero (iterateFrobenius R 2 n).toAddMonoidHom y b
      (by
        change iterateFrobenius R 2 n (iterateFrobenius R 2 n y - y) =
          iterateFrobenius R 2 n y - y
        rw [he, map_neg, hdn]) hny
    change b • (iterateFrobenius R 2 n y - y) = 0 at hz
    simpa only [he, smul_neg, neg_eq_zero] using hz
  have hz : d = 0 := by
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hab.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hax)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hby)
  refine ⟨sub_eq_zero.mp hz, ?_⟩
  rw [hd] at hz
  exact (sub_eq_zero.mp hz).symm
end MIPRE.LowDegree.BinaryFiniteField
