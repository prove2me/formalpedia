-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:11.352007+00:00
-- url     : https://prove2.me/submissions/a5763386-4c91-4e76-a51d-b3d506548e0c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean (solution of MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.FieldTheory.Finite.Extension
import Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_mem_range_iff_pow_card

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryFiniteField
open Polynomial
theorem _root_.solution {K L : Type*} [Field K] [Field L]
    [Finite K] [Algebra K L] [Algebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L]
    (t : ℕ) (hK : Nat.card K = 2 ^ (2 ^ t))
    (hL : Module.finrank (ZMod 2) L = 2 ^ (t + 1)) (x : L)
    (hx : x ∉ (algebraMap K L).range) :
    (minpoly (ZMod 2) x).natDegree = 2 ^ (t + 1) := by
  have hi : IsIntegral (ZMod 2) x := IsIntegral.of_finite (ZMod 2) x
  have hd : (minpoly (ZMod 2) x).natDegree ∣ 2 ^ (t + 1) := hL ▸ minpoly.degree_dvd hi
  obtain ⟨j, hj, hdeg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  by_cases heq : j = t + 1
  · simpa [heq] using hdeg
  have hjt : j ≤ t := by omega
  have hd' : (minpoly (ZMod 2) x).natDegree ∣ 2 ^ t := by
    rw [hdeg]
    exact pow_dvd_pow 2 hjt
  have hp := (minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd'
  have hpzero : aeval x (X ^ (Nat.card (ZMod 2)) ^ (2 ^ t) - X : (ZMod 2)[X]) = 0 := by
    exact (minpoly.dvd_iff).1 hp
  have hfix : x ^ Nat.card K = x := by
    simpa only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card,
      sub_eq_zero, hK] using hpzero
  exact False.elim (hx ((mem_range_iff_pow_card x).2 hfix))
end MIPRE.LowDegree.BinaryFiniteField
