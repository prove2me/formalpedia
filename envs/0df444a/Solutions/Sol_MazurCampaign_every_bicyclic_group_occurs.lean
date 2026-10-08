-- Prove2me | solution 1 for MazurCampaign.every_bicyclic_group_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T08:21:23.287988+00:00
-- url     : https://prove2.me/submissions/97318416-7070-4e78-9a74-560e6246206f

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_good_reduction_card_bound
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/


namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance instDecidableEquationOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance instDecidableNonsingularOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm

instance instFinitePoint [Finite R] : Finite W'.Point :=
  .of_equiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

instance instFintypePointOfDecidableEq [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

end WeierstrassCurve.Affine

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

namespace MazurOccurrenceWitnesses

def c3 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def c3_point : c3.toAffine.Point :=
  .some (0) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c3, WeierstrassCurve.toAffine])

theorem c3_order : addOrderOf c3_point = 3 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 3)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_2 : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

def c2_2_point : c2_2.toAffine.Point :=
  .some (1) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_2, WeierstrassCurve.toAffine])

theorem c2_2_order : addOrderOf c2_2_point = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_2_second : c2_2.toAffine.Point :=
  .some (0) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_2, WeierstrassCurve.toAffine])

theorem c2_2_second_order : addOrderOf c2_2_second = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

theorem c2_2_independent : ∀ j : Fin 2, (j.val : ℕ) • c2_2_point ≠ c2_2_second := by
  intro j
  fin_cases j <;> decide +kernel

def c6 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1⟩

def c6_point : c6.toAffine.Point :=
  .some (2) (3) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c6, WeierstrassCurve.toAffine])

theorem c6_order : addOrderOf c6_point = 6 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 6)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -1⟩

def c2_point : c2.toAffine.Point :=
  .some (1) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2, WeierstrassCurve.toAffine])

theorem c2_order : addOrderOf c2_point = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c5 : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩

def c5_point : c5.toAffine.Point :=
  .some (0) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c5, WeierstrassCurve.toAffine])

theorem c5_order : addOrderOf c5_point = 5 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 5)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c4 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2, 1⟩

def c4_point : c4.toAffine.Point :=
  .some (0) (1) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c4, WeierstrassCurve.toAffine])

theorem c4_order : addOrderOf c4_point = 4 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_4 : WeierstrassCurve ℚ := ⟨1, 0, 0, -4, -1⟩

def c2_4_point : c2_4.toAffine.Point :=
  .some (5) (8) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_4, WeierstrassCurve.toAffine])

theorem c2_4_order : addOrderOf c2_4_point = 4 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_4_second : c2_4.toAffine.Point :=
  .some (-2) (1) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_4, WeierstrassCurve.toAffine])

theorem c2_4_second_order : addOrderOf c2_4_second = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

theorem c2_4_independent : ∀ j : Fin 4, (j.val : ℕ) • c2_4_point ≠ c2_4_second := by
  intro j
  fin_cases j <;> decide +kernel

def c7 : WeierstrassCurve ℚ := ⟨1, -1, 1, -3, 3⟩

def c7_point : c7.toAffine.Point :=
  .some (1) (0) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c7, WeierstrassCurve.toAffine])

theorem c7_order : addOrderOf c7_point = 7 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 7)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c8 : WeierstrassCurve ℚ := ⟨1, 1, 1, -4, 5⟩

def c8_point : c8.toAffine.Point :=
  .some (5) (9) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c8, WeierstrassCurve.toAffine])

theorem c8_order : addOrderOf c8_point = 8 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 8)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c9 : WeierstrassCurve ℚ := ⟨1, -1, 1, -14, 29⟩

def c9_point : c9.toAffine.Point :=
  .some (3) (1) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c9, WeierstrassCurve.toAffine])

theorem c9_order : addOrderOf c9_point = 9 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 9)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_6 : WeierstrassCurve ℚ := ⟨1, 0, 1, -19, 26⟩

def c2_6_point : c2_6.toAffine.Point :=
  .some (1) (2) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_6, WeierstrassCurve.toAffine])

theorem c2_6_order : addOrderOf c2_6_point = 6 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 6)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_6_second : c2_6.toAffine.Point :=
  .some (3) (-2) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_6, WeierstrassCurve.toAffine])

theorem c2_6_second_order : addOrderOf c2_6_second = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

theorem c2_6_independent : ∀ j : Fin 6, (j.val : ℕ) • c2_6_point ≠ c2_6_second := by
  intro j
  fin_cases j <;> decide +kernel

def c10 : WeierstrassCurve ℚ := ⟨1, 0, 0, -45, 81⟩

def c10_point : c10.toAffine.Point :=
  .some (0) (9) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c10, WeierstrassCurve.toAffine])

theorem c10_order : addOrderOf c10_point = 10 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 10)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c12 : WeierstrassCurve ℚ := ⟨1, -1, 1, -122, 1721⟩

def c12_point : c12.toAffine.Point :=
  .some (-9) (49) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c12, WeierstrassCurve.toAffine])

theorem c12_order : addOrderOf c12_point = 12 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 12)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_8 : WeierstrassCurve ℚ := ⟨1, 0, 0, -1070, 7812⟩

def c2_8_point : c2_8.toAffine.Point :=
  .some (4) (58) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_8, WeierstrassCurve.toAffine])

theorem c2_8_order : addOrderOf c2_8_point = 8 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 8)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

def c2_8_second : c2_8.toAffine.Point :=
  .some (-36) (18) (by norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, c2_8, WeierstrassCurve.toAffine])

theorem c2_8_second_order : addOrderOf c2_8_second = 2 := by
  apply (addOrderOf_eq_iff (by decide : 0 < 2)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide +kernel

theorem c2_8_independent : ∀ j : Fin 8, (j.val : ℕ) • c2_8_point ≠ c2_8_second := by
  intro j
  fin_cases j <;> decide +kernel

end MazurOccurrenceWitnesses


namespace MazurOccurrenceWitnesses

/-- The cyclic homomorphism sending 1 to a point killed by n. -/
def pointZModHom {G : Type*} [AddCommGroup G] (n : ℕ) (P : G) (hP : n • P = 0) :
    ZMod n →+ G :=
  ZMod.lift n ⟨zmultiplesHom G P, by simpa using hP⟩

lemma pointZModHom_injective {G : Type*} [AddCommGroup G] (n : ℕ) (P : G)
    (hP : n • P = 0) (ho : addOrderOf P = n) :
    Function.Injective (pointZModHom n P hP) := by
  apply (ZMod.lift_injective n).mpr
  intro m hm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m n).mpr
  rw [← ho, addOrderOf_dvd_iff_zsmul_eq_zero]
  exact hm

/-- An injection of the desired finite group and a matching bound identify the
whole torsion subgroup. Consumers: the explicit cyclic and bicyclic witnesses. -/
lemma fullTorsionEquivOfInjection {E : WeierstrassCurve ℚ}
    {A : Type*} [AddCommGroup A] [Finite A]
    [Finite (MazurCampaign.RationalTorsion E)]
    (f : A →+ E.toAffine.Point) (hf : Function.Injective f)
    (hcard : Nat.card (MazurCampaign.RationalTorsion E) ≤ Nat.card A) :
    Nonempty (MazurCampaign.RationalTorsion E ≃+ A) := by
  let g : A →+ MazurCampaign.RationalTorsion E :=
    f.codRestrict (AddCommGroup.torsion E.toAffine.Point)
      (fun x ↦ f.isOfFinAddOrder (isOfFinAddOrder_of_finite x))
  have hg : Function.Injective g := by
    intro x y h
    exact hf (congrArg Subtype.val h)
  exact ⟨(AddEquiv.ofBijective g (hg.bijective_of_nat_card_le hcard)).symm⟩

end MazurOccurrenceWitnesses

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Witness coefficients were discovered in John Cremona's ecdata at commit
25cec5ecfec8b9f016eb1631ac633194c2bed39f. Database torsion claims are not
assumed: discriminants, point counts, reduction bounds and groups are proved.
-/
namespace MazurOccurrenceWitnesses
open WeierstrassCurve

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

def c1 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

def c1_integral : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩
lemma c1_map : c1_integral.map (Int.castRingHom ℚ) = c1 := by
  ext <;> simp [c1_integral, c1]

lemma c1_delta : c1_integral.Δ = 37 := by
  norm_num [c1_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c1.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c1_map,
    WeierstrassCurve.map_Δ, c1_delta]
  norm_num

instance : (c1_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c1_map]
  infer_instance

lemma c1_count_3 :
    Nat.card (c1_integral.map (Int.castRingHom (ZMod 3))).toAffine.Point = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c1_count_5 :
    Nat.card (c1_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c1_bound : Finite (MazurCampaign.RationalTorsion c1) ∧
    Nat.card (MazurCampaign.RationalTorsion c1) ≤ 1 := by
  have h0 := MazurCampaign.good_reduction_card_bound c1_integral 3
    (by decide) (by norm_num [c1_delta])
  rw [c1_map, c1_count_3] at h0
  have h1 := MazurCampaign.good_reduction_card_bound c1_integral 5
    (by decide) (by norm_num [c1_delta])
  rw [c1_map, c1_count_5] at h1
  refine ⟨h0.1, ?_⟩
  have h := Nat.dvd_gcd h0.2 h1.2
  norm_num only [Nat.gcd] at h
  exact Nat.le_of_dvd (by decide) h

def c3_integral : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, 0⟩
lemma c3_map : c3_integral.map (Int.castRingHom ℚ) = c3 := by
  ext <;> simp [c3_integral, c3]

lemma c3_delta : c3_integral.Δ = -27 := by
  norm_num [c3_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c3.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c3_map,
    WeierstrassCurve.map_Δ, c3_delta]
  norm_num

instance : (c3_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c3_map]
  infer_instance

lemma c3_count_5 :
    Nat.card (c3_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c3_count_7 :
    Nat.card (c3_integral.map (Int.castRingHom (ZMod 7))).toAffine.Point = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c3_bound : Finite (MazurCampaign.RationalTorsion c3) ∧
    Nat.card (MazurCampaign.RationalTorsion c3) ≤ 3 := by
  have h0 := MazurCampaign.good_reduction_card_bound c3_integral 5
    (by decide) (by norm_num [c3_delta])
  rw [c3_map, c3_count_5] at h0
  have h1 := MazurCampaign.good_reduction_card_bound c3_integral 7
    (by decide) (by norm_num [c3_delta])
  rw [c3_map, c3_count_7] at h1
  refine ⟨h0.1, ?_⟩
  have h := Nat.dvd_gcd h0.2 h1.2
  norm_num only [Nat.gcd] at h
  exact Nat.le_of_dvd (by decide) h

def c2_2_integral : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩
lemma c2_2_map : c2_2_integral.map (Int.castRingHom ℚ) = c2_2 := by
  ext <;> simp [c2_2_integral, c2_2]

lemma c2_2_delta : c2_2_integral.Δ = 64 := by
  norm_num [c2_2_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c2_2.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c2_2_map,
    WeierstrassCurve.map_Δ, c2_2_delta]
  norm_num

instance : (c2_2_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c2_2_map]
  infer_instance

lemma c2_2_count_3 :
    Nat.card (c2_2_integral.map (Int.castRingHom (ZMod 3))).toAffine.Point = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_2_bound : Finite (MazurCampaign.RationalTorsion c2_2) ∧
    Nat.card (MazurCampaign.RationalTorsion c2_2) ≤ 4 := by
  have h0 := MazurCampaign.good_reduction_card_bound c2_2_integral 3
    (by decide) (by norm_num [c2_2_delta])
  rw [c2_2_map, c2_2_count_3] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c6_integral : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, 1⟩
lemma c6_map : c6_integral.map (Int.castRingHom ℚ) = c6 := by
  ext <;> simp [c6_integral, c6]

lemma c6_delta : c6_integral.Δ = -432 := by
  norm_num [c6_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c6.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c6_map,
    WeierstrassCurve.map_Δ, c6_delta]
  norm_num

instance : (c6_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c6_map]
  infer_instance

lemma c6_count_5 :
    Nat.card (c6_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c6_bound : Finite (MazurCampaign.RationalTorsion c6) ∧
    Nat.card (MazurCampaign.RationalTorsion c6) ≤ 6 := by
  have h0 := MazurCampaign.good_reduction_card_bound c6_integral 5
    (by decide) (by norm_num [c6_delta])
  rw [c6_map, c6_count_5] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c2_integral : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, -1⟩
lemma c2_map : c2_integral.map (Int.castRingHom ℚ) = c2 := by
  ext <;> simp [c2_integral, c2]

lemma c2_delta : c2_integral.Δ = -432 := by
  norm_num [c2_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c2.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c2_map,
    WeierstrassCurve.map_Δ, c2_delta]
  norm_num

instance : (c2_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c2_map]
  infer_instance

lemma c2_count_5 :
    Nat.card (c2_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_count_7 :
    Nat.card (c2_integral.map (Int.castRingHom (ZMod 7))).toAffine.Point = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_bound : Finite (MazurCampaign.RationalTorsion c2) ∧
    Nat.card (MazurCampaign.RationalTorsion c2) ≤ 2 := by
  have h0 := MazurCampaign.good_reduction_card_bound c2_integral 5
    (by decide) (by norm_num [c2_delta])
  rw [c2_map, c2_count_5] at h0
  have h1 := MazurCampaign.good_reduction_card_bound c2_integral 7
    (by decide) (by norm_num [c2_delta])
  rw [c2_map, c2_count_7] at h1
  refine ⟨h0.1, ?_⟩
  have h := Nat.dvd_gcd h0.2 h1.2
  norm_num only [Nat.gcd] at h
  exact Nat.le_of_dvd (by decide) h

def c5_integral : WeierstrassCurve ℤ := ⟨0, -1, 1, 0, 0⟩
lemma c5_map : c5_integral.map (Int.castRingHom ℚ) = c5 := by
  ext <;> simp [c5_integral, c5]

lemma c5_delta : c5_integral.Δ = -11 := by
  norm_num [c5_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c5.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c5_map,
    WeierstrassCurve.map_Δ, c5_delta]
  norm_num

instance : (c5_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c5_map]
  infer_instance

lemma c5_count_3 :
    Nat.card (c5_integral.map (Int.castRingHom (ZMod 3))).toAffine.Point = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c5_bound : Finite (MazurCampaign.RationalTorsion c5) ∧
    Nat.card (MazurCampaign.RationalTorsion c5) ≤ 5 := by
  have h0 := MazurCampaign.good_reduction_card_bound c5_integral 3
    (by decide) (by norm_num [c5_delta])
  rw [c5_map, c5_count_3] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c4_integral : WeierstrassCurve ℤ := ⟨0, 0, 0, -2, 1⟩
lemma c4_map : c4_integral.map (Int.castRingHom ℚ) = c4 := by
  ext <;> simp [c4_integral, c4]

lemma c4_delta : c4_integral.Δ = 80 := by
  norm_num [c4_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c4.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c4_map,
    WeierstrassCurve.map_Δ, c4_delta]
  norm_num

instance : (c4_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c4_map]
  infer_instance

lemma c4_count_3 :
    Nat.card (c4_integral.map (Int.castRingHom (ZMod 3))).toAffine.Point = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c4_bound : Finite (MazurCampaign.RationalTorsion c4) ∧
    Nat.card (MazurCampaign.RationalTorsion c4) ≤ 4 := by
  have h0 := MazurCampaign.good_reduction_card_bound c4_integral 3
    (by decide) (by norm_num [c4_delta])
  rw [c4_map, c4_count_3] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c2_4_integral : WeierstrassCurve ℤ := ⟨1, 0, 0, -4, -1⟩
lemma c2_4_map : c2_4_integral.map (Int.castRingHom ℚ) = c2_4 := by
  ext <;> simp [c2_4_integral, c2_4]

lemma c2_4_delta : c2_4_integral.Δ = 3969 := by
  norm_num [c2_4_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c2_4.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c2_4_map,
    WeierstrassCurve.map_Δ, c2_4_delta]
  norm_num

instance : (c2_4_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c2_4_map]
  infer_instance

lemma c2_4_count_5 :
    Nat.card (c2_4_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_4_bound : Finite (MazurCampaign.RationalTorsion c2_4) ∧
    Nat.card (MazurCampaign.RationalTorsion c2_4) ≤ 8 := by
  have h0 := MazurCampaign.good_reduction_card_bound c2_4_integral 5
    (by decide) (by norm_num [c2_4_delta])
  rw [c2_4_map, c2_4_count_5] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c7_integral : WeierstrassCurve ℤ := ⟨1, -1, 1, -3, 3⟩
lemma c7_map : c7_integral.map (Int.castRingHom ℚ) = c7 := by
  ext <;> simp [c7_integral, c7]

lemma c7_delta : c7_integral.Δ = -1664 := by
  norm_num [c7_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c7.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c7_map,
    WeierstrassCurve.map_Δ, c7_delta]
  norm_num

instance : (c7_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c7_map]
  infer_instance

lemma c7_count_3 :
    Nat.card (c7_integral.map (Int.castRingHom (ZMod 3))).toAffine.Point = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c7_bound : Finite (MazurCampaign.RationalTorsion c7) ∧
    Nat.card (MazurCampaign.RationalTorsion c7) ≤ 7 := by
  have h0 := MazurCampaign.good_reduction_card_bound c7_integral 3
    (by decide) (by norm_num [c7_delta])
  rw [c7_map, c7_count_3] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c8_integral : WeierstrassCurve ℤ := ⟨1, 1, 1, -4, 5⟩
lemma c8_map : c8_integral.map (Int.castRingHom ℚ) = c8 := by
  ext <;> simp [c8_integral, c8]

lemma c8_delta : c8_integral.Δ = -16128 := by
  norm_num [c8_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c8.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c8_map,
    WeierstrassCurve.map_Δ, c8_delta]
  norm_num

instance : (c8_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c8_map]
  infer_instance

lemma c8_count_5 :
    Nat.card (c8_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c8_bound : Finite (MazurCampaign.RationalTorsion c8) ∧
    Nat.card (MazurCampaign.RationalTorsion c8) ≤ 8 := by
  have h0 := MazurCampaign.good_reduction_card_bound c8_integral 5
    (by decide) (by norm_num [c8_delta])
  rw [c8_map, c8_count_5] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c9_integral : WeierstrassCurve ℤ := ⟨1, -1, 1, -14, 29⟩
lemma c9_map : c9_integral.map (Int.castRingHom ℚ) = c9 := by
  ext <;> simp [c9_integral, c9]

lemma c9_delta : c9_integral.Δ = -124416 := by
  norm_num [c9_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c9.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c9_map,
    WeierstrassCurve.map_Δ, c9_delta]
  norm_num

instance : (c9_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c9_map]
  infer_instance

lemma c9_count_5 :
    Nat.card (c9_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c9_bound : Finite (MazurCampaign.RationalTorsion c9) ∧
    Nat.card (MazurCampaign.RationalTorsion c9) ≤ 9 := by
  have h0 := MazurCampaign.good_reduction_card_bound c9_integral 5
    (by decide) (by norm_num [c9_delta])
  rw [c9_map, c9_count_5] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c2_6_integral : WeierstrassCurve ℤ := ⟨1, 0, 1, -19, 26⟩
lemma c2_6_map : c2_6_integral.map (Int.castRingHom ℚ) = c2_6 := by
  ext <;> simp [c2_6_integral, c2_6]

lemma c2_6_delta : c2_6_integral.Δ = 72900 := by
  norm_num [c2_6_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c2_6.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c2_6_map,
    WeierstrassCurve.map_Δ, c2_6_delta]
  norm_num

instance : (c2_6_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c2_6_map]
  infer_instance

lemma c2_6_count_7 :
    Nat.card (c2_6_integral.map (Int.castRingHom (ZMod 7))).toAffine.Point = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_6_bound : Finite (MazurCampaign.RationalTorsion c2_6) ∧
    Nat.card (MazurCampaign.RationalTorsion c2_6) ≤ 12 := by
  have h0 := MazurCampaign.good_reduction_card_bound c2_6_integral 7
    (by decide) (by norm_num [c2_6_delta])
  rw [c2_6_map, c2_6_count_7] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c10_integral : WeierstrassCurve ℤ := ⟨1, 0, 0, -45, 81⟩
lemma c10_map : c10_integral.map (Int.castRingHom ℚ) = c10 := by
  ext <;> simp [c10_integral, c10]

lemma c10_delta : c10_integral.Δ = 2737152 := by
  norm_num [c10_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c10.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c10_map,
    WeierstrassCurve.map_Δ, c10_delta]
  norm_num

instance : (c10_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c10_map]
  infer_instance

lemma c10_count_5 :
    Nat.card (c10_integral.map (Int.castRingHom (ZMod 5))).toAffine.Point = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c10_bound : Finite (MazurCampaign.RationalTorsion c10) ∧
    Nat.card (MazurCampaign.RationalTorsion c10) ≤ 10 := by
  have h0 := MazurCampaign.good_reduction_card_bound c10_integral 5
    (by decide) (by norm_num [c10_delta])
  rw [c10_map, c10_count_5] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c12_integral : WeierstrassCurve ℤ := ⟨1, -1, 1, -122, 1721⟩
lemma c12_map : c12_integral.map (Int.castRingHom ℚ) = c12 := by
  ext <;> simp [c12_integral, c12]

lemma c12_delta : c12_integral.Δ = -1119744000 := by
  norm_num [c12_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c12.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c12_map,
    WeierstrassCurve.map_Δ, c12_delta]
  norm_num

instance : (c12_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c12_map]
  infer_instance

lemma c12_count_7 :
    Nat.card (c12_integral.map (Int.castRingHom (ZMod 7))).toAffine.Point = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c12_bound : Finite (MazurCampaign.RationalTorsion c12) ∧
    Nat.card (MazurCampaign.RationalTorsion c12) ≤ 12 := by
  have h0 := MazurCampaign.good_reduction_card_bound c12_integral 7
    (by decide) (by norm_num [c12_delta])
  rw [c12_map, c12_count_7] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

def c2_8_integral : WeierstrassCurve ℤ := ⟨1, 0, 0, -1070, 7812⟩
lemma c2_8_map : c2_8_integral.map (Int.castRingHom ℚ) = c2_8 := by
  ext <;> simp [c2_8_integral, c2_8]

lemma c2_8_delta : c2_8_integral.Δ = 51438240000 := by
  norm_num [c2_8_integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : c2_8.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, ← c2_8_map,
    WeierstrassCurve.map_Δ, c2_8_delta]
  norm_num

instance : (c2_8_integral.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [c2_8_map]
  infer_instance

lemma c2_8_count_11 :
    Nat.card (c2_8_integral.map (Int.castRingHom (ZMod 11))).toAffine.Point = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma c2_8_bound : Finite (MazurCampaign.RationalTorsion c2_8) ∧
    Nat.card (MazurCampaign.RationalTorsion c2_8) ≤ 16 := by
  have h0 := MazurCampaign.good_reduction_card_bound c2_8_integral 11
    (by decide) (by norm_num [c2_8_delta])
  rw [c2_8_map, c2_8_count_11] at h0
  refine ⟨h0.1, ?_⟩
  exact Nat.le_of_dvd (by decide) h0.2

end MazurOccurrenceWitnesses

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
namespace MazurOccurrenceWitnesses

def c1_hom : ZMod 1 →+ c1.toAffine.Point := 0

lemma c1_hom_injective : Function.Injective c1_hom := by
  intro x y h
  exact Subsingleton.elim x y

lemma c1_full_group : Nonempty (MazurCampaign.RationalTorsion c1 ≃+ ZMod 1) := by
  letI := c1_bound.1
  apply fullTorsionEquivOfInjection c1_hom c1_hom_injective
  simpa only [Nat.card_zmod] using c1_bound.2

def c3_hom : ZMod 3 →+ c3.toAffine.Point :=
  pointZModHom 3 c3_point (by decide +kernel)

lemma c3_hom_injective : Function.Injective c3_hom :=
  pointZModHom_injective 3 c3_point (by decide +kernel) c3_order

lemma c3_full_group : Nonempty (MazurCampaign.RationalTorsion c3 ≃+ ZMod 3) := by
  letI := c3_bound.1
  apply fullTorsionEquivOfInjection c3_hom c3_hom_injective
  simpa only [Nat.card_zmod] using c3_bound.2

def c2_2_hom : ZMod 2 × ZMod 2 →+ c2_2.toAffine.Point :=
  (pointZModHom 2 c2_2_second (by decide +kernel)).coprod
    (pointZModHom 2 c2_2_point (by decide +kernel))

lemma c2_2_hom_injective : Function.Injective c2_2_hom := by
  decide +kernel

lemma c2_2_full_group : Nonempty
    (MazurCampaign.RationalTorsion c2_2 ≃+ (ZMod 2 × ZMod 2)) := by
  letI := c2_2_bound.1
  apply fullTorsionEquivOfInjection c2_2_hom c2_2_hom_injective
  simpa only [Nat.card_prod, Nat.card_zmod] using c2_2_bound.2

def c6_hom : ZMod 6 →+ c6.toAffine.Point :=
  pointZModHom 6 c6_point (by decide +kernel)

lemma c6_hom_injective : Function.Injective c6_hom :=
  pointZModHom_injective 6 c6_point (by decide +kernel) c6_order

lemma c6_full_group : Nonempty (MazurCampaign.RationalTorsion c6 ≃+ ZMod 6) := by
  letI := c6_bound.1
  apply fullTorsionEquivOfInjection c6_hom c6_hom_injective
  simpa only [Nat.card_zmod] using c6_bound.2

def c2_hom : ZMod 2 →+ c2.toAffine.Point :=
  pointZModHom 2 c2_point (by decide +kernel)

lemma c2_hom_injective : Function.Injective c2_hom :=
  pointZModHom_injective 2 c2_point (by decide +kernel) c2_order

lemma c2_full_group : Nonempty (MazurCampaign.RationalTorsion c2 ≃+ ZMod 2) := by
  letI := c2_bound.1
  apply fullTorsionEquivOfInjection c2_hom c2_hom_injective
  simpa only [Nat.card_zmod] using c2_bound.2

def c5_hom : ZMod 5 →+ c5.toAffine.Point :=
  pointZModHom 5 c5_point (by decide +kernel)

lemma c5_hom_injective : Function.Injective c5_hom :=
  pointZModHom_injective 5 c5_point (by decide +kernel) c5_order

lemma c5_full_group : Nonempty (MazurCampaign.RationalTorsion c5 ≃+ ZMod 5) := by
  letI := c5_bound.1
  apply fullTorsionEquivOfInjection c5_hom c5_hom_injective
  simpa only [Nat.card_zmod] using c5_bound.2

def c4_hom : ZMod 4 →+ c4.toAffine.Point :=
  pointZModHom 4 c4_point (by decide +kernel)

lemma c4_hom_injective : Function.Injective c4_hom :=
  pointZModHom_injective 4 c4_point (by decide +kernel) c4_order

lemma c4_full_group : Nonempty (MazurCampaign.RationalTorsion c4 ≃+ ZMod 4) := by
  letI := c4_bound.1
  apply fullTorsionEquivOfInjection c4_hom c4_hom_injective
  simpa only [Nat.card_zmod] using c4_bound.2

def c2_4_hom : ZMod 2 × ZMod 4 →+ c2_4.toAffine.Point :=
  (pointZModHom 2 c2_4_second (by decide +kernel)).coprod
    (pointZModHom 4 c2_4_point (by decide +kernel))

lemma c2_4_hom_injective : Function.Injective c2_4_hom := by
  decide +kernel

lemma c2_4_full_group : Nonempty
    (MazurCampaign.RationalTorsion c2_4 ≃+ (ZMod 2 × ZMod 4)) := by
  letI := c2_4_bound.1
  apply fullTorsionEquivOfInjection c2_4_hom c2_4_hom_injective
  simpa only [Nat.card_prod, Nat.card_zmod] using c2_4_bound.2

def c7_hom : ZMod 7 →+ c7.toAffine.Point :=
  pointZModHom 7 c7_point (by decide +kernel)

lemma c7_hom_injective : Function.Injective c7_hom :=
  pointZModHom_injective 7 c7_point (by decide +kernel) c7_order

lemma c7_full_group : Nonempty (MazurCampaign.RationalTorsion c7 ≃+ ZMod 7) := by
  letI := c7_bound.1
  apply fullTorsionEquivOfInjection c7_hom c7_hom_injective
  simpa only [Nat.card_zmod] using c7_bound.2

def c8_hom : ZMod 8 →+ c8.toAffine.Point :=
  pointZModHom 8 c8_point (by decide +kernel)

lemma c8_hom_injective : Function.Injective c8_hom :=
  pointZModHom_injective 8 c8_point (by decide +kernel) c8_order

lemma c8_full_group : Nonempty (MazurCampaign.RationalTorsion c8 ≃+ ZMod 8) := by
  letI := c8_bound.1
  apply fullTorsionEquivOfInjection c8_hom c8_hom_injective
  simpa only [Nat.card_zmod] using c8_bound.2

def c9_hom : ZMod 9 →+ c9.toAffine.Point :=
  pointZModHom 9 c9_point (by decide +kernel)

lemma c9_hom_injective : Function.Injective c9_hom :=
  pointZModHom_injective 9 c9_point (by decide +kernel) c9_order

lemma c9_full_group : Nonempty (MazurCampaign.RationalTorsion c9 ≃+ ZMod 9) := by
  letI := c9_bound.1
  apply fullTorsionEquivOfInjection c9_hom c9_hom_injective
  simpa only [Nat.card_zmod] using c9_bound.2

def c2_6_hom : ZMod 2 × ZMod 6 →+ c2_6.toAffine.Point :=
  (pointZModHom 2 c2_6_second (by decide +kernel)).coprod
    (pointZModHom 6 c2_6_point (by decide +kernel))

lemma c2_6_hom_injective : Function.Injective c2_6_hom := by
  decide +kernel

lemma c2_6_full_group : Nonempty
    (MazurCampaign.RationalTorsion c2_6 ≃+ (ZMod 2 × ZMod 6)) := by
  letI := c2_6_bound.1
  apply fullTorsionEquivOfInjection c2_6_hom c2_6_hom_injective
  simpa only [Nat.card_prod, Nat.card_zmod] using c2_6_bound.2

def c10_hom : ZMod 10 →+ c10.toAffine.Point :=
  pointZModHom 10 c10_point (by decide +kernel)

lemma c10_hom_injective : Function.Injective c10_hom :=
  pointZModHom_injective 10 c10_point (by decide +kernel) c10_order

lemma c10_full_group : Nonempty (MazurCampaign.RationalTorsion c10 ≃+ ZMod 10) := by
  letI := c10_bound.1
  apply fullTorsionEquivOfInjection c10_hom c10_hom_injective
  simpa only [Nat.card_zmod] using c10_bound.2

def c12_hom : ZMod 12 →+ c12.toAffine.Point :=
  pointZModHom 12 c12_point (by decide +kernel)

lemma c12_hom_injective : Function.Injective c12_hom :=
  pointZModHom_injective 12 c12_point (by decide +kernel) c12_order

lemma c12_full_group : Nonempty (MazurCampaign.RationalTorsion c12 ≃+ ZMod 12) := by
  letI := c12_bound.1
  apply fullTorsionEquivOfInjection c12_hom c12_hom_injective
  simpa only [Nat.card_zmod] using c12_bound.2

def c2_8_hom : ZMod 2 × ZMod 8 →+ c2_8.toAffine.Point :=
  (pointZModHom 2 c2_8_second (by decide +kernel)).coprod
    (pointZModHom 8 c2_8_point (by decide +kernel))

lemma c2_8_hom_injective : Function.Injective c2_8_hom := by
  decide +kernel

lemma c2_8_full_group : Nonempty
    (MazurCampaign.RationalTorsion c2_8 ≃+ (ZMod 2 × ZMod 8)) := by
  letI := c2_8_bound.1
  apply fullTorsionEquivOfInjection c2_8_hom c2_8_hom_injective
  simpa only [Nat.card_prod, Nat.card_zmod] using c2_8_bound.2

end MazurOccurrenceWitnesses

theorem solution :
    ∀ m ∈ MazurCampaign.bicyclicParameters,
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
        Nonempty (MazurCampaign.RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m))) := by
  intro m hm
  simp only [MazurCampaign.bicyclicParameters, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨MazurOccurrenceWitnesses.c2_2, inferInstance, MazurOccurrenceWitnesses.c2_2_full_group⟩
  · exact ⟨MazurOccurrenceWitnesses.c2_4, inferInstance, MazurOccurrenceWitnesses.c2_4_full_group⟩
  · exact ⟨MazurOccurrenceWitnesses.c2_6, inferInstance, MazurOccurrenceWitnesses.c2_6_full_group⟩
  · exact ⟨MazurOccurrenceWitnesses.c2_8, inferInstance, MazurOccurrenceWitnesses.c2_8_full_group⟩

#print axioms solution
