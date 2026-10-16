-- Prove2me | solution 1 for OAI.ComplexCancellation.Rigidity.orbit_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:29:47.015122+00:00
-- url     : https://prove2.me/submissions/aaf9086b-1a2e-4aeb-9aae-fdf1c31f5069

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Rigidity.lean:L27-L43
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rigidity.orbit_coprime. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation

-- ---- from OAI.Algebra.AffineCancellation.Rigidity ----
namespace OAI

noncomputable section

/-! Polynomial orbit rigidity from the Mason–Stothers theorem. -/
namespace ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type*} [Field k]

/-- A polynomial of degree at most one has no nonunit square divisor. -/
lemma isUnit_of_square_dvd {n t : k[X]} (hn : n ≠ 0) (hdeg : n.natDegree ≤ 1)
    (ht : t ^ 2 ∣ n) : IsUnit t := by
  have ht0 : t ≠ 0 := by
    intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_dvd_iff] at ht
    exact hn ht
  have hb := natDegree_le_of_dvd ht hn
  rw [natDegree_pow] at hb
  have htdeg : t.natDegree = 0 := by omega
  rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree ht0, htdeg]
  rfl

/-- Coprimality of the square and cube terms of an affine-linear orbit sum. -/
lemma orbit_coprime {a d u n : k[X]} (hn : n ≠ 0) (hdeg : n.natDegree ≤ 1)
    (heq : d ^ 2 + a ^ 2 * u ^ 3 = n) : IsCoprime (d ^ 2) (a ^ 2 * u ^ 3) := by
  have hda : IsRelPrime d a := by
    intro t htd hta
    apply isUnit_of_square_dvd hn hdeg
    rw [← heq]
    exact dvd_add (pow_dvd_pow_of_dvd htd 2)
      (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hta 2) _)
  have hdu : IsRelPrime d u := by
    intro t htd htu
    apply isUnit_of_square_dvd hn hdeg
    rw [← heq]
    apply dvd_add (pow_dvd_pow_of_dvd htd 2)
    exact dvd_mul_of_dvd_right
      ((pow_dvd_pow_of_dvd htu 2).trans (pow_dvd_pow u (by decide : 2 ≤ 3))) _
  exact (hda.isCoprime.pow_left.pow_right).mul_right (hdu.isCoprime.pow_left.pow_right)

end ComplexCancellation.Rigidity

namespace ComplexCancellation.Rigidity

end ComplexCancellation.Rigidity

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rigidity.orbit_coprime := @_root_.OAI.ComplexCancellation.Rigidity.orbit_coprime
