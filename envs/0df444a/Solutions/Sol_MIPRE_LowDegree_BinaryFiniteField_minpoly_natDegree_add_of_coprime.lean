-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:42.800558+00:00
-- url     : https://prove2.me/submissions/9bddcaad-9640-4a66-ba72-c0b9b104fc68

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (solution of MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_frobenius_period_add_of_coprime

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryFiniteField
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
/-- Binary minimal degree divides exactly the Frobenius periods of an integral element. -/
theorem minpoly_natDegree_dvd_iff_frobenius (x : L) (hx : IsIntegral (ZMod 2) x) (n : ℕ) :
    (minpoly (ZMod 2) x).natDegree ∣ n ↔ x ^ (2 ^ n) = x := by
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  simp only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card, sub_eq_zero]
end
end MIPRE.LowDegree.BinaryFiniteField

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
theorem _root_.solution (x y : L)
    (hx : IsIntegral (ZMod 2) x) (hy : IsIntegral (ZMod 2) y)
    (hab : (minpoly (ZMod 2) x).natDegree.Coprime (minpoly (ZMod 2) y).natDegree) :
    (minpoly (ZMod 2) (x + y)).natDegree =
      (minpoly (ZMod 2) x).natDegree * (minpoly (ZMod 2) y).natDegree := by
  let : CharP L 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) L).injective 2
  let a := (minpoly (ZMod 2) x).natDegree
  let b := (minpoly (ZMod 2) y).natDegree
  let n := (minpoly (ZMod 2) (x + y)).natDegree
  have hsum := hx.add hy
  have hax : iterateFrobenius L 2 a x = x :=
    (minpoly_natDegree_dvd_iff_frobenius x hx a).mp dvd_rfl
  have hby : iterateFrobenius L 2 b y = y :=
    (minpoly_natDegree_dvd_iff_frobenius y hy b).mp dvd_rfl
  have hns : iterateFrobenius L 2 n (x + y) = x + y :=
    (minpoly_natDegree_dvd_iff_frobenius (x + y) hsum n).mp dvd_rfl
  obtain ⟨hnx, hny⟩ := frobenius_period_add_of_coprime x y a b n hab hax hby hns
  have han : a ∣ n := (minpoly_natDegree_dvd_iff_frobenius x hx n).mpr hnx
  have hbn : b ∣ n := (minpoly_natDegree_dvd_iff_frobenius y hy n).mpr hny
  have h₁ : a * b ∣ n := hab.mul_dvd_of_dvd_of_dvd han hbn
  have h₂ : n ∣ a * b := by
    apply (minpoly_natDegree_dvd_iff_frobenius (x + y) hsum (a * b)).mpr
    change iterateFrobenius L 2 (a * b) (x + y) = x + y
    rw [map_add]
    have hpx : iterateFrobenius L 2 (a * b) x = x := by
      rw [iterateFrobenius_mul_apply]
      exact Function.IsFixedPt.iterate hax b
    have hpy : iterateFrobenius L 2 (a * b) y = y := by
      rw [Nat.mul_comm a b, iterateFrobenius_mul_apply]
      exact Function.IsFixedPt.iterate hby a
    rw [hpx, hpy]
  exact Nat.dvd_antisymm h₂ h₁
end MIPRE.LowDegree.BinaryFiniteField
