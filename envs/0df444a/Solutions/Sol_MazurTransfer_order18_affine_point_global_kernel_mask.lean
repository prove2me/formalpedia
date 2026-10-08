-- Prove2me | solution 1 for MazurTransfer.order18_affine_point_global_kernel_mask
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T17:10:57.187382+00:00
-- url     : https://prove2.me/submissions/ae09593d-1372-4514-b047-c4fd08b08da6

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Definitions.Def_MazurTransfer_Order18KernelGeneratorSupportCertificate
import Theorems.Thm_MazurTransfer_order18_original_generator_support_certificate
import Theorems.Thm_MazurTransfer_order18_original_global_norm_kernel_enumeration
import Theorems.Thm_MazurTransfer_order18_original_kernel_representative_injective
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
import Theorems.Thm_MazurTransfer_order18_rational_cubics_irreducible
import Theorems.Thm_MazurTransfer_order18_relative_two_division_irreducible
import Theorems.Thm_MazurTransfer_order18_compositum_integers_principal
import Theorems.Thm_MazurTransfer_order18_supported_selmer_cardinality_256
import Theorems.Thm_MazurTransfer_order18_actual_dyadic_valuation_certificate
import Theorems.Thm_MazurTransfer_order18_normalized_cubic_unique_root
import Theorems.Thm_MazurTransfer_order18_dyadic_candidate_nonsquare
open scoped WeierstrassCurve WeierstrassCurve.Affine
namespace MazurTorsion.XOneEighteenRealCubicQuotient
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTransfer.order18_rational_cubics_irreducible.1
end MazurTorsion.XOneEighteenRealCubicQuotient
namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic
theorem twoDivisionPolynomial_irreducible : Irreducible twoDivisionPolynomial :=
  MazurTransfer.order18_rational_cubics_irreducible.2
end MazurTorsion.XOneEighteenTwoDivisionArithmetic
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
theorem relativePolynomial_irreducible : Irreducible relativePolynomial :=
  MazurTransfer.order18_relative_two_division_irreducible
end MazurTorsion.XOneEighteenTwoDivisionClassNumber
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumberOne
theorem compositumRingOfIntegers_isPrincipal :
    IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M) :=
  MazurTransfer.order18_compositum_integers_principal
end MazurTorsion.XOneEighteenTwoDivisionClassNumberOne
namespace MazurTorsion.XOneEighteenGlobalSelmerBridge
theorem natCard_dyadicSelmerM
    (hprincipal : IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M))
    (V : DyadicValuationCertificate) : Nat.card DyadicSelmerM = 256 :=
  MazurTransfer.order18_supported_selmer_cardinality_256
end MazurTorsion.XOneEighteenGlobalSelmerBridge
namespace MazurTorsion.XOneEighteenDyadicValuationCertificate
noncomputable def dyadicValuationCertificate :
    MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicValuationCertificate :=
  Classical.choice MazurTransfer.order18_actual_dyadic_valuation_certificate
end MazurTorsion.XOneEighteenDyadicValuationCertificate
namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
theorem normalizedRelativeCubicValue_eq_zero_iff :
    ∀ z : Fin 3 → R, normalizedRelativeCubicValue z = 0 ↔
      z = MazurTorsion.XOneEighteenDyadicGeneratorCertificate.normalizedGenerator :=
  MazurTransfer.order18_normalized_cubic_unique_root
end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
namespace MazurTorsion.XOneEighteenDyadicCubicCertificate
theorem candidate_nonsquare : ∀ i : Fin 15, ¬ IsSquare (candidate i) :=
  MazurTransfer.order18_dyadic_candidate_nonsquare
end MazurTorsion.XOneEighteenDyadicCubicCertificate
namespace MazurTorsion.XOneEighteenQuotientRankZero
end MazurTorsion.XOneEighteenQuotientRankZero
namespace MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
end MazurTorsion.XOneEighteenQuotientReductionAtSeventeen

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
end MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
namespace MazurTorsion.XOneEighteenGlobalSelmerBridge
private theorem h1_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h1 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.1
private theorem h2_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h2 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.1
private theorem h3_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h3 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.1
private theorem h4_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h4 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.2
end MazurTorsion.XOneEighteenGlobalSelmerBridge

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel
end MazurTorsion.XOneEighteenTwoDivisionIntegralModel
namespace MazurTorsion.XOneEighteenDyadicKernelSeparation
theorem kernelRepresentative_injective : Function.Injective
    MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative :=
  MazurTransfer.order18_original_kernel_representative_injective
end MazurTorsion.XOneEighteenDyadicKernelSeparation

namespace MazurTorsion.XOneEighteenDescent
private noncomputable abbrev concreteKernelSupportCertificate :
    MazurTorsion.XOneEighteenGlobalSelmerBridge.KernelGeneratorSupportCertificate :=
  Classical.choice MazurTransfer.order18_original_generator_support_certificate
end MazurTorsion.XOneEighteenDescent



namespace MazurTorsion.XOneEighteenDyadicCompletionBridge
end MazurTorsion.XOneEighteenDyadicCompletionBridge

namespace MazurTorsion.XOneEighteenKernelGeneratorSupport
end MazurTorsion.XOneEighteenKernelGeneratorSupport

namespace MazurTorsion.XOneEighteenFinalRankZero
end MazurTorsion.XOneEighteenFinalRankZero


/- Source module: EllipticCurves.Mathlib.Basic. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Material for Mathlib

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section

section Group

variable {G H : Type*} [Group G] [Group H]

/-- A map `f` between groups with `f 1 = 1` that sends triples with product `1` to triples
with product `1` is a homomorphism. Useful when a map is naturally defined via a symmetric
ternary relation, like collinearity on a cubic curve. -/
@[to_additive /-- A map `f` between additive groups with `f 0 = 0` that sends triples with
sum `0` to triples with sum `0` is a homomorphism. Useful when a map is naturally defined via
a symmetric ternary relation, like collinearity on a cubic curve. -/]
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group







end Group

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩



end Units

section modPow







namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp



/-- The class of a unit is trivial in `Units.modPow α 2` exactly when the unit is a square
in `α`. -/
lemma mk_eq_one_iff_isSquare {u : αˣ} :
    (QuotientGroup.mk u : Units.modPow α 2) = 1 ↔ IsSquare (u : α) := by
  rw [mk_eq_one_iff]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [← hw]; push_cast [sq]; rfl⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ u.isUnit)
  exact ⟨hsu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, ← hs])⟩

@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩







@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl





lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← mk'_apply, map_mk']
  exact congrArg _ (Units.ext rfl)







/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n



end Units.modPow

end modPow

section Ideal



end Ideal

section LinearAlgebra







end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}



/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma Valuation.eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma Valuation.map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial of positive degree with coefficients that are integral for the
valuation `ν` is itself integral. (This is a concrete form of the fact that valuation rings are
integrally closed.) -/
lemma Valuation.le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  by_contra! hlt
  have h := ν.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]











/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- If the valuation of a unit `u` is the `n`-th power of the valuation of a unit `z`, then the
`v`-adic order of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R)
    {n : ℕ} {u z : Kˣ} (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, EmbeddingLike.map_eq_one_iff]
  refine (QuotientGroup.eq_one_iff _).trans ?_
  rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← hk]; ring⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; ring⟩⟩







variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]



-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.


-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement


/-- The prime of `R` lying below a prime `w` of an integral extension `B`. -/
def IsDedekindDomain.HeightOneSpectrum.below [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := Ideal.IsPrime.under R w.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot R w.ne_bot



instance IsDedekindDomain.HeightOneSpectrum.instLiesOverBelow [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.below R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.below R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.below R, hw, rfl⟩⟩
  rwa [show w.below R = v from HeightOneSpectrum.ext hva.symm]



/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)



-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only


namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]



variable {A}



end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/-- The height-one prime of `B` obtained by contracting a height-one prime along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero. -/
def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them


variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

/-- The `w`-adic valuation of `φ u` is the valuation of `u` at the contracted prime, raised
to a fixed positive power (the ramification index), for an embedding `φ` of fraction fields
compatible with an embedding `ψ` of Dedekind domains. -/
theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := by
    have h : Function.Injective ((algebraMap C N).comp ψ) := by
      rw [hcomp]
      exact φ.injective.comp (IsFractionRing.injective B L)
    exact fun x y hxy ↦ h (by simp only [RingHom.comp_apply, hxy])
  have ht1 : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have ht2 : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have htf : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have hlie : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  refine ⟨(comapOfNeBot ψ w hne).asIdeal.ramificationIdx' w.asIdeal, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq, Units.coe_map,
    MonoidHom.coe_coe]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

/-- Divisibility of adic valuations transports along compatible embeddings: if the valuation
of `u` at the contracted prime is divisible by `n`, so is the `w`-adic valuation of `φ u`. -/
theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℕ} (u : Lˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  rw [he u, toAdd_pow, nsmul_eq_mul]
  exact h.mul_left _



end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`.
Note the absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
lemma resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  rw [show C x - X = C (-1 : R) * (X - C x) by simp, resultant_C_mul_right, h,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  convert resultant_add_right_deg g 1 g.natDegree 0 n (by simp)
  · simp
  rw [← C_1, resultant_C_zero_right, one_pow, mul_one, hg.coeff_natDegree, one_pow]

/-- For monic `g`, the resultant does not depend on the size parameter used for the second
argument, as long as it is at least its degree. -/
lemma Monic.resultant_congr_right (hg : g.Monic) {p : R[X]} {n₁ n₂ : ℕ}
    (h₁ : p.natDegree ≤ n₁) (h₂ : n₁ ≤ n₂) :
    g.resultant p g.natDegree n₂ = g.resultant p g.natDegree n₁ := by
  rw [← Nat.add_sub_cancel' h₂, resultant_add_right_deg _ _ _ _ _ h₁, hg.coeff_natDegree,
    one_pow, one_mul]

private lemma succ_mul_div_two {n : ℕ} (hn : 0 < n) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [mul_comm m] at hk
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring, hk]
  lia

private lemma resultant_X_sub_C_add_mul_derivative (hdeg : 0 < g.natDegree) (x : R) :
    (X - C x).resultant (g + (X - C x) * derivative g) 1 g.natDegree = g.eval x := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [resultant_add_mul_right _ _ _ _ _ hd' (natDegree_X_sub_C_le x),
    resultant_X_sub_C_left _ _ _ le_rfl]

private lemma resultant_add_mul_derivative [Nontrivial R] (hg : g.Monic)
    (hdeg : 0 < g.natDegree) (x : R) :
    g.resultant (g + (X - C x) * derivative g) g.natDegree g.natDegree =
      (-1) ^ g.natDegree * g.eval x *
        g.resultant (derivative g) g.natDegree (g.natDegree - 1) := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [show g + (X - C x) * derivative g = (X - C x) * derivative g + g * 1 by ring,
    resultant_add_mul_right _ _ _ _ _ (by simp) le_rfl,
    hg.resultant_congr_right natDegree_mul_le (by rw [natDegree_X_sub_C]; lia),
    resultant_mul_right g (X - C x) (derivative g) g.natDegree le_rfl, natDegree_X_sub_C,
    resultant_X_sub_C_right _ _ _ le_rfl,
    ← hg.resultant_congr_right (n₂ := g.natDegree - 1) le_rfl (natDegree_derivative_le g)]

/-- The discriminant of `(X - C x) * g` for monic `g` of positive degree is
`g.discr * g.eval x ^ 2`. -/
theorem discr_X_sub_C_mul (hg : g.Monic) (hdeg : 0 < g.natDegree) (x : R) :
    ((X - C x) * g).discr = g.discr * g.eval x ^ 2 := by
  nontriviality R
  have hmon : ((X - C x) * g).Monic := (monic_X_sub_C x).mul hg
  have hN : ((X - C x) * g).natDegree = g.natDegree + 1 := by
    rw [(monic_X_sub_C x).natDegree_mul hg, natDegree_X_sub_C, add_comm]
  have hder : derivative ((X - C x) * g) = g + (X - C x) * derivative g := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hDle : (g + (X - C x) * derivative g).natDegree ≤ g.natDegree :=
    (natDegree_add_le _ _).trans (max_le le_rfl (natDegree_mul_le.trans
      (by rw [natDegree_X_sub_C]; have := natDegree_derivative_le g; lia)))
  -- compare the splitting of `Res((X - C x) * g, ((X - C x) * g)')` along the product with
  -- its expression through the discriminant
  have hsplit := resultant_mul_left (X - C x) g (g + (X - C x) * derivative g) g.natDegree hDle
  rw [natDegree_X_sub_C, add_comm 1 g.natDegree] at hsplit
  have hres := resultant_deriv (f := (X - C x) * g)
    (by rw [← natDegree_pos_iff_degree_pos, hN]; lia)
  rw [hN, hder, hmon.leadingCoeff, mul_one, Nat.add_sub_cancel, succ_mul_div_two hdeg,
    pow_add] at hres
  have hres2 := resultant_deriv (f := g) (natDegree_pos_iff_degree_pos.mp hdeg)
  rw [hg.leadingCoeff, mul_one] at hres2
  have hmain := hres.symm.trans hsplit
  rw [resultant_X_sub_C_add_mul_derivative hdeg x, resultant_add_mul_derivative hg hdeg x,
    hres2] at hmain
  -- now peel off the signs, which cancel
  have hpow (k : ℕ) : ((-1 : R) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  set s : R := (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)
  set t : R := (-1) ^ g.natDegree
  have hs : s * s = 1 := hpow _
  have ht : t * t = 1 := hpow _
  calc ((X - C x) * g).discr
      = s * t * (s * t * ((X - C x) * g).discr) := by
        rw [← mul_assoc, mul_mul_mul_comm, hs, ht, one_mul, one_mul]
    _ = s * t * (g.eval x * (t * g.eval x * (s * g.discr))) := by rw [hmain]
    _ = s * s * (t * t) * (g.discr * g.eval x ^ 2) := by ring
    _ = g.discr * g.eval x ^ 2 := by rw [hs, ht, one_mul, one_mul]

lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]



section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the
map that `mk g : R[X]_(g.natDegree) ≃ₗ AdjoinRoot g` turns into multiplication by `mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is
`q ↦ (q %ₘ g, q /ₘ g)`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · intro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

/-- The inverse of `Ψ` is division with remainder by `g`. -/
lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    change g * (w.2 : R[X]) + 1 * (w.1 : R[X]) = _
    simp
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester



end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)





/-- `mk g` is a linear equivalence from the polynomials of degree `< g.natDegree` onto
`AdjoinRoot g`, for `g` monic. -/
noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · intro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl



/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]



section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)



end Map

end AdjoinRoot



/-! ### The norm on a product algebra -/





section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by `Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

/-- If `f` itself is monic and irreducible, then its only factor is `f`. -/
lemma coe_eq (hf : Irreducible f) (hmon : f.Monic) (p : f.Factors) : (p : K[X]) = f :=
  Polynomial.eq_of_monic_of_associated p.monic hmon (p.irreducible.associated_of_dvd hf p.dvd)

/-- A monic irreducible polynomial has itself as its only monic irreducible factor. -/
@[reducible]
def unique (hf : Irreducible f) (hmon : f.Monic) : Unique f.Factors where
  default := ⟨f, hmon, hf, dvd_rfl⟩
  uniq p := Subtype.ext (coe_eq hf hmon p)





lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

/-- Membership in `normalizedFactors` (with its normalization from `DecidableEq K`) is
equivalent to being a monic irreducible factor. -/
lemma mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂ ▸ monic_normalize h₁.ne_zero, h₁, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁.normalize_eq_self, h₃⟩⟩

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective





lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  -- identify `f.Factors` with the subtype of the `Finset` of normalized factors
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf



lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm



end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite





lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]



open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X]/(f)` is the product of the fields `K[X]/(p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl



/-- The projection of `K[X]/(f)` onto the field factor `K[X]/(p)`. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

/-- The `n`-th power classes of units of `K[X]/(f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors
(`Units.map` version of `modPowEquivPiFactors_unit`). -/
@[simp]
lemma modPowEquivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (QuotientGroup.mk u) p =
      QuotientGroup.mk (Units.map (projFactor hf hsq p).toMonoidHom u) := by
  have h := modPowEquivPiFactors_unit hf hsq n u.isUnit p
  rw [show u.isUnit.unit = u from Units.ext rfl] at h
  exact h.trans (congrArg QuotientGroup.mk (Units.ext rfl))







end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]





variable [NumberField K] [FiniteDimensional K L]









end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]









end Discriminant

end

end


/- Source module: EllipticCurves.X18WeakMordellWeil. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


section

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite, where `E` is an elliptic curve
given by a Weierstrass equation `y² = x³ + a₂x² + a₄x + a₆ =: f(x)` (so with `a₁ = a₃ = 0`,
which is always achievable when the characteristic is not `2`)
over the fraction field `K` of a Dedekind domain `R`, under finiteness hypotheses — finite
class group and finitely generated unit group for the rings of integers of the field factors
of `K[X]/⟨f⟩` — that are theorems when `K` is a number field.

We use the `x-T` map approach.

The general-purpose material developed along the way, which has nothing to do with elliptic
curves, lives in `EllipticCurves.Mathlib.Basic`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
4. Show that `ker μ = 2E(K)`.
   => done.
5. Show that `im μ` is contained in the kernel of the norm map on square classes.
   => done, via `AdjoinRoot.norm_mk_eq_resultant`, which says that the norm of
   `AdjoinRoot.mk g p` for monic `g` is the resultant of `g` and `p`
   (in `EllipticCurves.Mathlib.Basic`).
   Note that this step is *not* needed for the finiteness result (Steps 6 and 7 do not use
   it); it is included because the norm condition cuts down the Selmer group in explicit
   computations.
6. Show that `im μ ⊆ A(S,2)` for a suitable finite set `S` of "bad" primes.
   => done, as `range_μ_le_selmerGroupA` at the end of the file, for `E` over the fraction field
   of a Dedekind domain and for *any* `S` outside which the coefficients of the cubic are
   integral and `disc f` is a unit. Such sets are provided by `badPrimes` (primes dividing `2`
   or `Δ`, or occurring in a coefficient denominator); the refined sets `discBadPrimes` and
   `badPrimes₂` defined alongside it feed the sharpened Selmer-group bound of
   `EllipticCurves.SelmerGroup`.
7. Show that `A(S,2)` is finite, and conclude that `E(K)/2E(K)` is finite.
   This generic finiteness step is deliberately omitted from this X18 slice. The explicit
   X18 certificate supplies the finite square-class calculation instead; this file stops at
   `range_μ_le_selmerGroupA`.
-/

/-!
### Two commutative-ring identities

These are used in Step 3 (`μ` is a homomorphism); they encode the multiplicativity of the
`x - T` map on the level of coordinates.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)



/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero



lemma degree_f : W.f.degree = 3 := by
  rw [degree_eq_natDegree W.f_ne_zero, natDegree_f]; rfl

/-- The discriminant of the cubic `f`, in terms of the coefficients of `W`. -/
lemma discr_f : W.f.discr = W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆
    - 27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three W.degree_f]
  simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- In char ≠ 2 normal form, `Δ = 16 · disc f`; in particular the two agree up to a unit away
from `2`, but *not* at even places, where `disc f` is the finer invariant. -/
lemma Δ_eq_discr_f [W.IsCharNeTwoNF] : W.Δ = 16 * W.f.discr := by
  rw [Δ_of_isCharNeTwoNF W, W.discr_f]; ring



lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring



lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [separable_def', derivative_f, f]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄ - 96 * W.a₂ ^ 2) * X
      + C (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (32 * W.a₂ ^ 2 - 96 * W.a₄) * X ^ 2
      + C (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * X
      + C (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)), ?_⟩
  rw [mul_assoc, mul_assoc (C (W.Δ)⁻¹), ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isCharNeTwoNF]
  simp only [C_eq_algebraMap]
  algebra

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]



/-- On a point of `W`, the value `f x` is a square, so it vanishes exactly when `y` does. -/
lemma ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!



lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp only [fCofactor, f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow,
    map_mul, add_sub_add_right_eq_sub]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma discr_fCofactor (x : K) :
    (W.fCofactor x).discr = (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) := by
  have hdeg : (W.fCofactor x).degree = 2 := by
    rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, W.natDegree_fCofactor x]; rfl
  rw [discr_of_degree_eq_two hdeg]
  simp only [fCofactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- If `x` is a root of `f`, splitting off the factor `X - x` writes `disc f` as
`(fCofactor x).discr * f'(x) ^ 2`. -/
lemma discr_f_eq_discr_fCofactor_mul_sq {x : K} (hx : W.f.eval x = 0) :
    W.f.discr = (W.fCofactor x).discr * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx, mul_comm]
  rw [discr_X_sub_C_mul (W.monic_fCofactor x) (by rw [W.natDegree_fCofactor]; norm_num) x,
    W.eval_fCofactor_self x]

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/


lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  rw [eval_f] at hx
  have := W.Δ_of_isCharNeTwoNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  linear_combination ((288 * W.a₄ - 96 * W.a₂ ^ 2) * x
      + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) * hx
    + ((32 * W.a₂ ^ 2 - 96 * W.a₄) * x ^ 2 + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * x
      + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) * this

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]





/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)



/-- The norm of `x - θ` is `f x`. -/
lemma norm_mk_C_sub_X (x : K) : Algebra.norm K (AdjoinRoot.mk W.f (C x - X)) = W.f.eval x := by
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hd, resultant_C_sub_X _ _ _ le_rfl]

/-- If `x` is a root of `f`, then the norm of `x - θ + fCofactor x`, which is the element
representing `f' θ` in this case, is the square `(f' x)²`. -/
lemma norm_mk_C_sub_X_add_fCofactor {x : K} (hx : W.f.eval x = 0) :
    Algebra.norm K (AdjoinRoot.mk W.f (C x - X + W.fCofactor x))
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  have hq : (W.fCofactor x).natDegree = 2 := W.natDegree_fCofactor x
  have hqx : (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ :=
    W.eval_fCofactor_self x
  have hp : (C x - X + W.fCofactor x).natDegree = 2 := by
    simp only [fCofactor]
    compute_degree!
  have hpx : (C x - X + W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, ← hqx]
    simp
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hp, W.natDegree_f]
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx]
  rw [show (3 : ℕ) = (W.fCofactor x).natDegree + (X - C x).natDegree by
        rw [hq, natDegree_X_sub_C],
    resultant_mul_left _ _ _ 2 hp.le, hq, natDegree_X_sub_C]
  -- the factor coming from `X - C x` is `p.eval x`
  rw [show (X - C x) = (X - C x) ^ 1 by rw [pow_one],
    resultant_X_sub_C_pow_left _ _ _ _ hp.le, pow_one, hpx]
  -- the factor coming from `fCofactor x` is `(C x - X).resultant`, since `fCofactor x ≡ 0`
  have hres : (W.fCofactor x).resultant (C x - X) 2 2 = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    have h := resultant_add_right_deg (W.fCofactor x) (C x - X) 2 1 1 (by compute_degree!)
    simp only [show (1 : ℕ) + 1 = 2 from rfl, pow_one] at h
    rw [h, show (W.fCofactor x).coeff 2 = 1 by
        rw [← hq]; exact (W.monic_fCofactor x).coeff_natDegree,
      one_mul, resultant_C_sub_X _ _ _ hq.le, hqx]
  rw [show C x - X + W.fCofactor x = (C x - X) + W.fCofactor x * 1 by ring,
    resultant_add_mul_right (W.fCofactor x) (C x - X) 1 2 2 (by simp) hq.le, hres]
  ring





/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl



lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <|
    C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))) =
      C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * ·) using
      mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp




end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/
noncomputable instance : CommGroup W.M := inferInstance

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]



variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/


variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl



/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/






section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h







end kernel





/-!
### The `2`-torsion of the group of points

In our situation (`a₁ = a₃ = 0`, so `-(x, y) = (x, -y)`), the `2`-torsion consists of the
origin together with the points `(x, 0)` at the roots of `f`; in particular its order is
the number of roots of `f` in `K` plus one.
-/







/-!
### Step 5: show that `im μ` is contained in the kernel of the norm map.

The norm `Algebra.norm K : W.A →* K` sends units to units, hence induces a homomorphism
`normM : W.M →* Units.modPow K 2` on square classes. We must show `normM ∘ μ = 1`.

Writing `f = (X - θ₁) * (X - θ₂) * (X - θ₃)` over a splitting field, the two cases are:

* if `f x ≠ 0`, then `N (x - θ) = ∏ᵢ (x - θᵢ) = f x = y²`, a square;
* if `f x = 0`, then `N (f' θ) = (f' x)²`, again a square.

Both are instances of `AdjoinRoot.norm_mk_eq_resultant`: the norm of `AdjoinRoot.mk g p` for
monic `g` is the resultant of `g` and `p`. See `norm_mk_C_sub_X` and
`norm_mk_C_sub_X_add_fCofactor` in Step 1 above, which deduce them from it by resultant algebra;
in the second case the factorization `f = fCofactor x * (X - C x)` splits the resultant into two
factors, each equal to `(W.fCofactor x).eval x = f' x`.

`AdjoinRoot.norm_mk_eq_resultant` is proved in `EllipticCurves.Mathlib.Basic`; it is a general fact
about
`AdjoinRoot g` for monic `g` and looks worth upstreaming.
-/

section Step5

/-- The norm map on square classes, induced by `Algebra.norm K : W.A →* K`. -/
noncomputable def normM : W.M →* Units.modPow K 2 :=
  Units.modPow.map (Algebra.norm K) 2

/-- The image of `μX` lies in the kernel of the norm map on square classes. -/
lemma normM_μX_eq_one {x y : K} (h : W.Equation x y) : W.normM (W.μX x) = 1 := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨3 * x ^ 2 + 2 * W.a₂ * x + W.a₄, (W.norm_mk_C_sub_X_add_fCofactor hx).symm⟩
  · rw [μX_of_eval_f_ne_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨y, by rw [W.norm_mk_C_sub_X, (equation_iff_eval_f_eq_sq W x y).mp h]⟩

@[simp]
lemma normM_μ₀_eq_one (P : W.Point) : W.normM (W.μ₀ P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => exact normM_μX_eq_one h.1

/-- The image of `μ` is contained in the kernel of the norm map on square classes. -/
lemma range_μ_le_ker_normM : (μ (W := W)).range ≤ (normM (W := W)).ker := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [MonoidHom.mem_ker, μ_apply]
  exact normM_μ₀_eq_one P

end Step5

end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
Weierstrass equation with `a₁ = a₃ = 0`. Everything Step 6 needs — a height-one spectrum,
the `v`-adic
valuations, and unique factorization of fractional ideals — is exactly the Dedekind package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The way around this is the decomposition of `A` into a product of fields,
provided by `EllipticCurves.Mathlib.Basic`: as `f` is separable, `AdjoinRoot.equivPiFactors` gives
`A ≃ₐ[K] ((p : W.f.Factors) → AdjoinRoot p)`, a finite product of finite separable field
extensions of `K` indexed by the monic irreducible factors `p` of `f`, and correspondingly
`AdjoinRoot.modPowEquivPiFactors` gives
`W.M = Units.modPow A 2 ≃* ((p : W.f.Factors) → Units.modPow (AdjoinRoot p) 2)`.
Each factor carries `Field`, `Algebra K` and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability.

With that in hand:

* for each factor, `ringOfIntegersFactor R p := integralClosure R (AdjoinRoot p)` is again a
  Dedekind domain (`IsIntegralClosure.isDedekindDomain`, applicable thanks to
  `AdjoinRoot.isSeparable_of_separable`) with fraction field `AdjoinRoot p`, so
  `IsDedekindDomain.selmerGroup` applies to it;
* `A(S,2)` (`selmerGroupA`) is the preimage under the above isomorphism of the product of the
  `selmerGroupFactor R p`, the `2`-Selmer groups relative to the primes above `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `ringOfIntegersFactor R p` not above `S`, the valuation `w (x - θ)` is even, where `θ` is
  the root of `p`. If `x` has a pole at `w`, the leading term of the cubic dominates and
  `w (x - θ) = w x = w (y / x) ^ 2`. If `x` is `w`-integral, one uses the factorization
  `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over the factor `K[X]/(p)`
  itself: the cofactor
  is congruent to `f' θ` modulo `x - θ`, and `f' θ` is a `w`-unit because `w ∤ Δ`. So either
  `x - θ` is a `w`-unit, or the cofactor is, and then `w (x - θ) = w y ^ 2`.

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of the `2`-Selmer group of each
factor, which needs the primes above `S` to be finite in number, the class group of
`ringOfIntegersFactor R p` to be finite, and its unit group to be finitely generated — i.e.
number fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

Note that the valuation computation stays inside the single field factor `K[X]/(p)`; no
splitting field is needed. That `f' θ` is a unit at every good prime
(`valuation_deriv_root_eq_one`) needs exactly that the coefficients of the cubic are integral
and `disc f` is a unit there — which is what `Δ ∈ badPrimes` buys, via the Bézout identity
behind `separable_f`.

All of this is carried out below: `badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to
each factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `selmerGroupA` (`A(S,2)`, as a subgroup of `W.M`), and
finally `range_μ_le_selmerGroupA`.
-/

section Cubic

/- Specializations of `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`
from `EllipticCurves.Mathlib.Basic` to the monic cubic `t ^ 3 + a * t ^ 2 + b * t + c`. They are
specific to Weierstrass equations, so they live here rather than in the general-support file. -/

open Polynomial

variable {L Γ : Type*} [CommRing L] [Nontrivial L] [LinearOrderedCommGroupWithZero Γ]
  (ν : Valuation L Γ) {t a b c : L}

private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

private lemma Valuation.map_cubic_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa using h

private lemma Valuation.le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) (by rw [hdeg]; norm_num) ?_
  simpa using heq

end Cubic

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

-- Step 6 needs neither `DecidableEq K` (except where the `x - T` map `μX` enters at the very
-- end) nor the group structure on points, so we re-declare the variables rather than
-- inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to Step 6: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X]/(p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the
image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])





















section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}































end BadPrimes

section DerivativeUnit

/- `f'(x)` is a unit at a rational root `x` of `f` whenever the coefficients are integral and
the valuation of `disc f` is `1` or `exp (-1)`: this is the arithmetic input for the
`2`-torsion `x - T` representative, both at good primes and at primes with
`v(disc f) = exp (-1)`. -/



open WithZero in
private lemma eq_one_of_le_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1)
    (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h2
  rw [← exp_log ht0] at h1 h2 ⊢
  rw [← exp_nsmul, two_nsmul] at h2
  rw [← exp_zero] at h1
  rw [exp_eq_one]
  have h1' := exp_le_exp.mp h1
  have h2' := exp_le_exp.mp h2
  lia

open WithZero in
/-- If `x` is a rational root of `f` and the coefficients of the cubic are `ν`-integral with
`exp (-1) ≤ ν (disc f)`, then `f'(x)` is a `ν`-unit: `disc f = (fCofactor x).discr * f'(x)²`
with both factors integral, and the square `ν (f'(x))²` cannot equal `exp (-1)`. -/
lemma valuation_deriv_eval_eq_one (ν : Valuation K ℤᵐ⁰) {x : K} (hx : W.f.eval x = 0)
    (ha₂ : ν W.a₂ ≤ 1) (ha₄ : ν W.a₄ ≤ 1) (ha₆ : ν W.a₆ ≤ 1)
    (hd : exp (-1) ≤ ν W.f.discr) :
    ν (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : ν x ≤ 1 := by
    rw [eval_f] at hx
    exact ν.le_one_of_root_cubic ha₂ ha₄ ha₆ hx
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ ν.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) ha₂) hx1)) ha₄
  have hcd' : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ ν.integer :=
    sub_mem (pow_mem (add_mem hx1 ha₂) 2) (mul_mem (ofNat_mem _ 4)
      (add_mem (add_mem (pow_mem hx1 2) (mul_mem ha₂ hx1)) ha₄))
  have hcd : ν (W.fCofactor x).discr ≤ 1 := by rw [W.discr_fCofactor x]; exact hcd'
  rw [W.discr_f_eq_discr_fCofactor_mul_sq hx, map_mul, map_pow] at hd
  exact eq_one_of_le_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X]/(p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure
of `R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

/-- The `w`-adic valuation of an element of `K` is the `v`-adic valuation of the prime `v`
below `w`, raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (w.below R).valuation K z ^ ((w.below R).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation (𝕃 p) (ι p z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime below `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (w.below R).valuation K z ≤ 1) :
    w.valuation (𝕃 p) (ι p z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- A prime `w` of the ring of integers of a field factor that does not lie above `S` lies
over a prime of `R` outside `S`. -/
lemma below_notMem_of_notMem_primesAbove [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {S : Set (HeightOneSpectrum R)} {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) : w.below R ∉ S :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X]/(p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    θ p ^ 3 + ι p W.a₂ * θ p ^ 2 + ι p W.a₄ * θ p + ι p W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The Bézout identity behind `separable_f` at the level of `disc f`, evaluated at `θ`:
`f′(θ)` times an explicit quadratic in `θ` with integral coefficients equals `disc f`.
(The classical identity with `Δ` on the right is `16` times this one; this version stays
useful at even places.) -/
lemma deriv_root_mul_eq_discr_f (p : W.f.Factors) :
    (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄)
        * ((2 * ι p W.a₂ ^ 2 - 6 * ι p W.a₄) * θ p ^ 2
          + (2 * ι p W.a₂ ^ 3 - 7 * ι p W.a₂ * ι p W.a₄ + 9 * ι p W.a₆) * θ p
          + (ι p W.a₂ ^ 2 * ι p W.a₄ - 4 * ι p W.a₄ ^ 2 + 3 * ι p W.a₂ * ι p W.a₆)) =
      ι p W.f.discr := by
  have hd : ι p W.f.discr = ι p W.a₂ ^ 2 * ι p W.a₄ ^ 2 - 4 * ι p W.a₄ ^ 3
      - 4 * ι p W.a₂ ^ 3 * ι p W.a₆ - 27 * ι p W.a₆ ^ 2
      + 18 * ι p W.a₂ * ι p W.a₄ * ι p W.a₆ := by
    rw [W.discr_f]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  rw [hd]
  linear_combination (-(18 * ι p W.a₄ - 6 * ι p W.a₂ ^ 2) * θ p
    - (15 * ι p W.a₂ * ι p W.a₄ - 4 * ι p W.a₂ ^ 3 - 27 * ι p W.a₆)) * W.root_cubic_eq_zero p

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X]/(p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      θ p ^ 2 + (ι p x + ι p W.a₂) * θ p + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1) (hd : (w.below R).valuation K W.f.discr = 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then the root `θ` is
`w`-integral: it satisfies the monic cubic `f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one : w.valuation (𝕃 p) (θ p) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_algebraMap_le_one R p w ha₂)
    (W.valuation_algebraMap_le_one R p w ha₄)
    (W.valuation_algebraMap_le_one R p w ha₆)
    (W.root_cubic_eq_zero p)

/-- An element of `K` with trivial valuation at the prime below `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K} (hz : (w.below R).valuation K z = 1) :
    w.valuation (𝕃 p) (ι p z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then `f' θ` is
`w`-integral. -/
lemma valuation_deriv_root_le_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) ≤ 1 := by
  have ht := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h : 3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄ ∈ (w.valuation (𝕃 p)).integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem ht 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) (W.valuation_algebraMap_le_one R p w ha₂)) ht))
      (W.valuation_algebraMap_le_one R p w ha₄)
  exact h

include ha₂ ha₄ ha₆ hd in
/-- If the coefficients of the cubic are integral and `disc f` is a unit at the prime below
`w`, then `f' θ = 3 θ ^ 2 + 2 a₂ θ + a₄` is a `w`-unit.

Evaluating the Bézout identity behind `separable_f` at `θ` gives `f'(θ) * c(θ) = disc f`
(`deriv_root_mul_eq_discr_f`) for an explicit quadratic `c` with `w`-integral coefficients.
Both factors are integral at `w` and the product is a unit, so both are units. -/
lemma valuation_deriv_root_eq_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  set B := algebraMap K L W.a₆
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- both factors in `deriv_root_mul_eq_discr_f` are integral, and their product is a unit
  have hD : ν (3 * t ^ 2 + 2 * A₂ * t + A) ≤ 1 :=
    W.valuation_deriv_root_le_one R p ha₂ ha₄ ha₆
  have hC : (2 * A₂ ^ 2 - 6 * A) * t ^ 2 + (2 * A₂ ^ 3 - 7 * A₂ * A + 9 * B) * t
      + (A₂ ^ 2 * A - 4 * A ^ 2 + 3 * A₂ * B) ∈ ν.integer := by
    refine add_mem (add_mem (mul_mem ?_ (pow_mem ht 2)) (mul_mem ?_ ht)) ?_
    · exact sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 2)) (mul_mem (ofNat_mem _ 6) hA)
    · exact add_mem (sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 3))
        (mul_mem (mul_mem (ofNat_mem _ 7) hA₂) hA)) (mul_mem (ofNat_mem _ 9) hB)
    · exact add_mem (sub_mem (mul_mem (pow_mem hA₂ 2) hA)
        (mul_mem (ofNat_mem _ 4) (pow_mem hA 2))) (mul_mem (mul_mem (ofNat_mem _ 3) hA₂) hB)
  refine ν.eq_one_of_mul_eq_one hD hC ?_
  rw [deriv_root_mul_eq_discr_f]
  exact W.valuation_algebraMap_eq_one R p hd

include ha₂ ha₄ ha₆ hderiv in
/-- If the coefficients of the cubic are integral at the prime below `w` and `f' θ` is a
`w`-unit, and if `x` is `w`-integral and `x - θ` is not a `w`-unit, then the cofactor
`x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄` is a `w`-unit: modulo `x - θ` it equals `f' θ`. -/
lemma valuation_cofactor_eq_one {x : K}
    (hx : w.valuation (𝕃 p) (ι p x) ≤ 1)
    (hlt : w.valuation (𝕃 p) (ι p x - θ p) < 1) :
    w.valuation (𝕃 p) (ι p x ^ 2 + θ p * ι p x + θ p ^ 2
      + ι p W.a₂ * (ι p x + θ p) + ι p W.a₄) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h2t : s + 2 * t + A₂ ∈ ν.integer :=
    add_mem (add_mem hx (mul_mem (ofNat_mem _ 2) ht)) hA₂
  have hlt' : ν ((s - t) * (s + 2 * t + A₂)) < ν (3 * t ^ 2 + 2 * A₂ * t + A) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show s ^ 2 + t * s + t ^ 2 + A₂ * (s + t) + A
      = (s - t) * (s + 2 * t + A₂) + (3 * t ^ 2 + 2 * A₂ * t + A) by ring,
    ν.map_add_eq_of_lt_right hlt', hderiv]

include ha₂ ha₄ ha₆ in
/-- If `x` is a root of `f`, then at a prime `w` at which (i.e. at the prime of `R` below
which) the coefficients of the cubic are integral and `f'(x)` is a unit, the `p`-component of
the `x - T` representative is a unit.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f'(x)`; if the cofactor vanishes
the component is `x - θ` and `f'(x) = (x - θ)(2x + θ + a₂)`. Either way `hdx` makes it a unit.

At a good prime, `hdx` is supplied by `valuation_deriv_eval_eq_one`; at an odd prime with
`v(disc f) = exp (-1)` the same lemma applies, so the `2`-torsion representative is unramified
there as well. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (w.below R).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation (𝕃 p) (ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x with hsdef
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- the `w`-unit `f'(x)`, transported to `L`
  have hderiv : ν (3 * s ^ 2 + 2 * A₂ * s + A) = 1 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat]
      using W.valuation_algebraMap_eq_one R p (w := w) hdx
  -- `x` is a root of the cubic too, hence integral at `w`
  have hs : s ^ 3 + A₂ * s ^ 2 + A * s + B = 0 := by
    rw [hsdef, hA₂def, hAdef, hBdef, ← W.map_eval_f, hx, map_zero]
  have hs1 : ν s ≤ 1 := ν.le_one_of_root_cubic hA₂ hA hB hs
  have hprod : (s - t) * (t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)) = 0 := by
    linear_combination hs - W.root_cubic_eq_zero p
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `x = θ`: the component is `f'(x)`
    rw [h0, zero_add, show t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
        = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -(t + 2 * s + A₂) * h0, hderiv]
  · -- the cofactor vanishes: the component is `x - θ`, and `f'(x) = (x - θ)(2x + θ + a₂)`
    rw [h0, add_zero]
    have hst : s - t ∈ ν.integer := sub_mem hs1 ht
    have h2t : 2 * s + t + A₂ ∈ ν.integer :=
      add_mem (add_mem (mul_mem (ofNat_mem _ 2) hs1) ht) hA₂
    refine ν.eq_one_of_mul_eq_one hst h2t ?_
    rw [show (s - t) * (2 * s + t + A₂) = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -h0,
      hderiv]

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu ha₂ ha₄ ha₆

/-- Non-integral case: `x` has a pole at the prime of `R` below `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < ν x` makes the
leading term of the cubic dominate: `ν (f x) = ν x ^ 3`, hence `ν y ^ 2 = ν x ^ 3`. Also
`ν θ ≤ 1 < ν x`
gives `ν (x - θ) = ν x`. Therefore `ν (x - θ) = ν (y / x) ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (𝕃 p) (ι p x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  have hx0 : algebraMap K L x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx'
    exact absurd hx' (by simp)
  have hx0' : ν (algebraMap K L x) ≠ 0 := ν.ne_zero_iff.mpr hx0
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  -- the Weierstrass equation, transported to `L`
  have heq : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hval : ν (algebraMap K L y) ^ 2 = ν (algebraMap K L x) ^ 3 := by
    rw [← map_pow, heq, ν.map_cubic_of_one_lt (W.valuation_algebraMap_le_one R p w ha₂)
      (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆) hx']
  -- `ν (x - θ) = ν x`, since `θ` is integral and `x` is not
  have hu' : ν (u : L) = ν (algebraMap K L x) := by
    rw [hu]
    exact Valuation.map_sub_eq_of_lt_left _ ((W.valuation_root_le_one R p ha₂ ha₄ ha₆).trans_lt hx')
  have hkey : ν (u : L) = ν ((Units.mk0 _ (div_ne_zero hy0 hx0) : Lˣ) : L) ^ 2 := by
    rw [hu', Units.val_mk0, map_div₀, div_pow, hval, eq_div_iff (pow_ne_zero 2 hx0'), mul_comm]
    exact (pow_succ _ 2).symm
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- Integral case: `x` is integral at the prime of `R` below `w`.

Over `L` the Weierstrass equation factors as `y ^ 2 = (x - θ) * c` with cofactor
`c = x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `ν (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a
`w`-unit, the cofactor is a `w`-unit. Hence `ν (x - θ) = ν y ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (𝕃 p) (ι p x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over `L`
  have heqL : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 + A₂ * algebraMap K L x ^ 2 +
      A * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [hA₂def, hAdef, ← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (u : L) * (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
        + A₂ * (algebraMap K L x + t) + A) =
      (algebraMap K L y) ^ 2 := by
    rw [hu]
    linear_combination -W.root_cubic_eq_zero p - heqL
  have hu1 : ν (u : L) ≤ 1 := by rw [hu]; exact ν.map_sub_le hx' ht
  by_cases hlt : ν (u : L) = 1
  · -- `x - θ` is a unit, so its valuation is trivially even
    have hkey : ν (u : L) = ν ((1 : Lˣ) : L) ^ 2 := by rw [Units.val_one, map_one, one_pow, hlt]
    simpa using w.dvd_toAdd_valuationOfNeZero hkey
  -- otherwise `w` divides `x - θ`, and then it cannot divide the cofactor
  replace hlt : ν (u : L) < 1 := lt_of_le_of_ne hu1 hlt
  rw [hu] at hlt
  have hcof : ν (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
      + A₂ * (algebraMap K L x + t) + A) = 1 :=
    W.valuation_cofactor_eq_one R p ha₂ ha₄ ha₆ hderiv hx' hlt
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have hkey : ν (u : L) = ν ((Units.mk0 _ hy0 : Lˣ) : L) ^ 2 := by
    rw [Units.val_mk0, ← map_pow, ← hfac, map_mul, hcof, mul_one]
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away:
for `(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X]/(p)` such that the coefficients of the cubic are integral at the prime of `R` below `w`
and `f' θ` is a `w`-unit, the `w`-adic valuation of `x - θ` is even.

The proof splits on whether `x` has a pole at the prime of `R` below `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (𝕃 p) (ι p x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w ha₂ ha₄ ha₆ hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w ha₂ ha₄ ha₆ hderiv
      (not_lt.mp hx')

end Core

section Selmer





variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The image of the generic `x - T` representative in the field factor `K[X]/(p)` is `x - θ`. -/
lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      ι p x - θ p := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

/-- The image of the `2`-torsion `x - T` representative in the field factor `K[X]/(p)`. -/
lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))

/-- The `2`-Selmer group of the field factor `AdjoinRoot p` of `W.A`, relative to the primes of
its ring of integers lying above the primes in `S`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow (𝕃 p) 2) :=
  IsDedekindDomain.selmerGroupAbove R (W.ringOfIntegersFactor R p) (𝕃 p) S 2

/-- `A(S,2)` in the product decomposition: the product of the `2`-Selmer groups of the field
factors of `W.A`. -/
noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow (𝕃 p) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R S)

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)` for `S` the bad primes. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R S).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R S ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R S p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]

/-!
#### The arithmetic input

Write `θ` for `AdjoinRoot.root p`, the image of the root `T` in the field factor `K[X]/(p)`,
and `𝓞` for the integral closure of `R` in `K[X]/(p)`, a Dedekind domain by
`isDedekindDomain_ringOfIntegersFactor` (an instance, in the `RingOfIntegers` section above).

The `p`-component of `μX x` is the square class of the reduction mod `p` of the `x - T`
representative, computed by `projFactor_mk_C_sub_X` and
`projFactor_mk_C_sub_X_add_fCofactor` below: it is `x - θ` in the generic case and
`x - θ + fCofactor x` when `x` is a root of `f`.

What has to be shown is that this class lies in the `2`-Selmer group of `K[X]/(p)`, i.e. that
`w (x - θ)` is even for every prime `w` of `𝓞` not lying above a prime of `S`; away from `S`,
the coefficients of the cubic are integral and `disc f` is a unit, by hypothesis.
The two cases are split off as `mem_selmerGroupFactor_of_eval_f_ne_zero` and
`mem_selmerGroupFactor_of_eval_f_eq_zero`.
-/

/-- Membership of the class of a unit in the `2`-Selmer group of a field factor: its valuation
is even at every prime of the ring of integers not lying above `S`. -/
lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : (𝕃 p)ˣ) :
    (QuotientGroup.mk u : Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
  forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u





variable (hSa₂ : ∀ v ∉ S, v.valuation K W.a₂ ≤ 1) (hSa₄ : ∀ v ∉ S, v.valuation K W.a₄ ≤ 1)
  (hSa₆ : ∀ v ∉ S, v.valuation K W.a₆ ≤ 1) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)

include hSa₂ hSa₄ hSa₆ hSd in
/-- Generic case of the arithmetic input: `f x ≠ 0`, so the `p`-component of `μX x` is the class
of `x - θ`. -/
lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_ w (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv)
    (W.valuation_deriv_root_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) (hSd _ hv))
  exact W.projFactor_mk_C_sub_X x p

include hSa₂ hSa₄ hSa₆ hSd in
/-- `2`-torsion case of the arithmetic input: `f x = 0`.

By `projFactor_mk_C_sub_X_add_fCofactor` the `p`-component of `μX x` is `x - θ + fCofactor x`,
which by `valuation_projFactor_torsion_eq_one` is a unit at every prime `w` not lying above
`S`. Its valuation is therefore `0`, in particular even. -/
lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0)
    (p : W.f.Factors) :
    (((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hd1 : WithZero.exp (-1 : ℤ) ≤ (w.below R).valuation K W.f.discr := by
    rw [hSd _ hv]
    exact (WithZero.exp_le_exp.mpr (by lia)).trans_eq WithZero.exp_zero
  have hval : w.valuation (𝕃 p) (u : 𝕃 p) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hx
      (W.valuation_deriv_eval_eq_one _ hx (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hd1)
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

section

variable [DecidableEq K]

include hSa₂ hSa₄ hSa₆ hSd in
/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X]/(p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R S hSa₂ hSa₄ hSa₆ hSd hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R S hSa₂ hSa₄ hSa₆ hSd h hx p

include hSa₂ hSa₄ hSa₆ hSd in
/-- **Step 6**: the image of `μ` is contained in `A(S,2)`, whenever the coefficients of the
cubic are integral and `disc f` is a unit away from `S`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R S hSa₂ hSa₄ hSa₆ hSd h.1 p

end

end Selmer

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The real-cubic elliptic quotient of the `X₁(18)` sextic

This file records an explicit elliptic quotient of the standard genus-two
model for `X₁(18)`.  Its coefficient field is the totally real cubic field
generated by a root `tau` of

`T³ - 3T - 1`.

Only the algebraic point map is proved here.  In particular, this file makes
no assertion about the Mordell--Weil rank or the rational points of the
elliptic curve.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenRealCubicQuotient

noncomputable section

/-! ## The cubic coefficient field -/























/-- The defining cubic relation in `K`. -/
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    AdjoinRoot.mk cubicPolynomial (X ^ 3 - 3 * X - 1 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul,
    map_ofNat, map_one, AdjoinRoot.mk_X] at h
  have h' : tau ^ 3 - 3 * tau - 1 = 0 := by
    simpa only [tau] using h
  linear_combination h'































/-! ## The elliptic quotient and its point map -/



/-- The quotient curve has discriminant `-2`. -/
theorem quotientCurve_discriminant : quotientCurve.Δ = -2 := by
  norm_num [quotientCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination
    (-16 * tau ^ 7 - 80 * tau ^ 6 - 103 * tau ^ 5 + 124 * tau ^ 4 +
      483 * tau ^ 3 + 545 * tau ^ 2 + 284 * tau + 61) *
      (tau_cubic)

instance quotientCurve_isElliptic : quotientCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, quotientCurve_discriminant]
  norm_num















/-! ## Change to the rational-coefficient model -/











end

end MazurTorsion.XOneEighteenRealCubicQuotient

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q





theorem tau_cubic : tau ^ 3 = 3 * tau + 1 :=
  MazurTorsion.XOneEighteenRealCubicQuotient.tau_cubic

end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/



theorem relativePolynomial_monic : relativePolynomial.Monic := by
  simp only [relativePolynomial]
  monicity <;> norm_num

theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 3 := by
  simp only [relativePolynomial]
  compute_degree!









/-- The coefficient-field relation remains exact after base change. -/
theorem t_cubic : t ^ 3 = 3 * t + 1 := by
  simpa only [t, map_pow, map_mul, map_ofNat, map_add, map_one] using
    congrArg (algebraMap Q.K M) Q.tau_cubic

/-- The defining relation in the relative cubic algebra. -/
theorem s_cubic : s ^ 3 = 3 * s + 10 := by
  have h : AdjoinRoot.mk relativePolynomial relativePolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk relativePolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial Q.K) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : s ^ 3 - 3 * s - 10 = 0 := by
    simpa only [s] using h
  linear_combination h'

/-- The relative cubic algebra has the expected rank `3` over `K`, without
using irreducibility. -/
theorem finrank_M_over_K : Module.finrank Q.K M = 3 := by
  rw [(AdjoinRoot.powerBasis' relativePolynomial_monic).finrank]
  exact relativePolynomial_natDegree



theorem relativeTwoDivisionZ_cubic :
    relativeTwoDivisionZ ^ 3 - 3 * relativeTwoDivisionZ ^ 2 +
        408 * relativeTwoDivisionZ + 80 = 0 := by
  simp only [relativeTwoDivisionZ]
  linear_combination
    (27 * s ^ 3 - 162 * s ^ 2 + 243 * s + 216) * s_cubic

/-! ## Exact relative norm certificates -/



theorem quadraticElement_eq (a b c : Q.K) :
    quadraticElement a b c =
      algebraMap Q.K M a * s ^ 2 + algebraMap Q.K M b * s +
        algebraMap Q.K M c := by
  simp [quadraticElement, s]





/-- Closed formula for the relative norm of a quadratic representative.
This is the determinant of multiplication in the basis `1,s,s²`. -/
theorem norm_quadraticElement (a b c : Q.K) :
    Algebra.norm Q.K (quadraticElement a b c) =
      100 * a ^ 3 - 30 * a ^ 2 * b + 9 * a ^ 2 * c -
        30 * a * b * c + 6 * a * c ^ 2 + 10 * b ^ 3 -
        3 * b ^ 2 * c + c ^ 3 := by
  let pb := AdjoinRoot.powerBasis' relativePolynomial_monic
  rw [quadraticElement_eq, Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_add, map_mul, map_pow]
  rw [(Algebra.leftMulMatrix pb.basis).commutes a,
    (Algebra.leftMulMatrix pb.basis).commutes b,
    (Algebra.leftMulMatrix pb.basis).commutes c]
  have hs : s = pb.gen := rfl
  rw [hs, pb.leftMulMatrix]
  have hmin : pb.minpolyGen = relativePolynomial := by
    dsimp [pb]
    rw [PowerBasis.minpolyGen_eq,
      AdjoinRoot.powerBasis'_gen,
      AdjoinRoot.minpoly_root relativePolynomial_monic.ne_zero,
      relativePolynomial_monic.leadingCoeff, inv_one, C_1, mul_one]
  rw [hmin]
  have hdim : pb.dim = 3 := relativePolynomial_natDegree
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) Q.K :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -relativePolynomial.coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) a *
          companion ^ 2 +
        algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) b *
          companion +
      algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) c) = _
  have hcompanion :
      Matrix.reindexAlgEquiv Q.K Q.K e companion =
        !![0, 0, 10; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, relativePolynomial, coeff_sub,
        coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv Q.K (R := Q.K) e]
  rw [map_add, map_add, map_mul, map_pow, map_mul]
  rw [(Matrix.reindexAlgEquiv Q.K Q.K e).commutes a,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes b,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes c]
  rw [hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring















end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Concrete norm certificates for the `X₁(18)` two-division algebra

This file evaluates the relative norms of the explicit squareclass
representatives used in the two-descent.  The proofs use only the determinant
formula from `XOneEighteenTwoDivisionArithmetic` and the defining cubic
relation for the coefficient generator.  In particular, no field structure on
the relative cubic algebra is used.
-/

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

private theorem tau_pow_four : Q.tau ^ 4 = 3 * Q.tau ^ 2 + Q.tau := by
  calc
    Q.tau ^ 4 = Q.tau * Q.tau ^ 3 := by ring
    _ = Q.tau * (3 * Q.tau + 1) := by rw [Q.tau_cubic]
    _ = 3 * Q.tau ^ 2 + Q.tau := by ring

private theorem tau_pow_five :
    Q.tau ^ 5 = Q.tau ^ 2 + 9 * Q.tau + 3 := by
  calc
    Q.tau ^ 5 = Q.tau * Q.tau ^ 4 := by ring
    _ = Q.tau * (3 * Q.tau ^ 2 + Q.tau) := by rw [tau_pow_four]
    _ = 3 * Q.tau ^ 3 + Q.tau ^ 2 := by ring
    _ = Q.tau ^ 2 + 9 * Q.tau + 3 := by rw [Q.tau_cubic]; ring

private theorem tau_pow_six :
    Q.tau ^ 6 = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by
  calc
    Q.tau ^ 6 = (Q.tau ^ 3) ^ 2 := by ring
    _ = (3 * Q.tau + 1) ^ 2 := by rw [Q.tau_cubic]
    _ = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by ring







/-- The first kernel representative has relative norm one. -/
theorem norm_h1 : Algebra.norm Q.K h1 = 1 := by
  rw [h1, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The second kernel representative has relative norm one. -/
theorem norm_h2 : Algebra.norm Q.K h2 = 1 := by
  rw [h2, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The third kernel representative has relative norm four. -/
theorem norm_h3 : Algebra.norm Q.K h3 = 4 := by
  rw [h3, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four, Q.tau_cubic]
  ring

/-- The fourth kernel representative has the displayed quadratic norm. -/
theorem norm_h4 :
    Algebra.norm Q.K h4 = 4 * (-Q.tau ^ 2 + Q.tau + 4) := by
  rw [h4, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four]
  ring

/-- The coefficient occurring in `norm_h4` is the advertised square after
using the coefficient cubic relation. -/
theorem four_mul_neg_tau_sq_add_tau_add_four_eq_square :
    4 * (-Q.tau ^ 2 + Q.tau + 4) = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [show (2 * (Q.tau ^ 2 - 2)) ^ 2 =
    4 * Q.tau ^ 4 - 16 * Q.tau ^ 2 + 16 by ring, tau_pow_four]
  ring

/-- The norm of `h4`, in a form immediately usable by squareclass code. -/
theorem norm_h4_eq_square :
    Algebra.norm Q.K h4 = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [norm_h4, four_mul_neg_tau_sq_add_tau_add_four_eq_square]



end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A characteristic-not-two model of the `X₁(18)` elliptic quotient

This file puts the real-cubic elliptic quotient into the form used by the
`x-T` two-descent.  Both coordinate changes are genuine admissible changes
of Weierstrass variables, so the resulting point maps are additive
equivalences rather than equation-only substitutions.

The completed two-division cubic is also identified with the explicit
relative cubic algebra used by the arithmetic certificates.  No
Mordell--Weil or Selmer conclusion is asserted here.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic









/-! ## Admissible point-group equivalences -/





/-- The characteristic-not-two model used by the `x-T` descent. -/
def descentCurve : WeierstrassCurve K :=
  rationalModel.toCharNeTwoNF • rationalModel



/-- The completed-square equation has coefficients
`[0,-3/4,0,51/2,5/4]`. -/
theorem descentCurve_eq :
    descentCurve =
      (⟨0, -(3 : K) / 4, 0, (51 : K) / 2, (5 : K) / 4⟩ :
        WeierstrassCurve K) := by
  ext <;>
    norm_num [descentCurve, rationalModel,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]











/-! ## The completed two-division cubic -/

/-- The monic cubic on the right-hand side of the completed-square model. -/
theorem descentCurve_f :
    descentCurve.toAffine.f =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 +
        C ((51 : K) / 2) * X + C ((5 : K) / 4) := by
  rw [descentCurve_eq]
  change
    X ^ 3 + C (-(3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4) =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4)
  have hneg : (-(3 : K) / 4) = -((3 : K) / 4) := by ring
  rw [hneg, map_neg]
  ring



/-- The explicit relative element is a root of the completed two-division
cubic. -/
theorem descentRootInM_isRoot :
    Polynomial.IsRoot
      (descentCurve.toAffine.f.map (algebraMap K M)) descentRootInM := by
  rw [Polynomial.IsRoot, descentCurve_f]
  rw [Polynomial.eval_map_algebraMap]
  simp only [aeval_add, aeval_sub, aeval_mul, map_pow, aeval_X,
    aeval_C]
  change
    descentRootInM ^ 3 -
        algebraMap K M ((3 : K) / 4) * descentRootInM ^ 2 +
      algebraMap K M ((51 : K) / 2) * descentRootInM +
        algebraMap K M ((5 : K) / 4) = 0
  have hcube :
      algebraMap K M (1 / 4 : K) ^ 3 =
        algebraMap K M (1 / 64 : K) := by
    rw [← map_pow]
    norm_num
  have hquad :
      algebraMap K M ((3 : K) / 4) *
          algebraMap K M (1 / 4 : K) ^ 2 =
        algebraMap K M (1 / 64 : K) * (3 : M) := by
    calc
      _ = algebraMap K M (((3 : K) / 4) * (1 / 4 : K) ^ 2) := by
        rw [← map_pow, ← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 3) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (3 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (3 : M) := by
        simp only [map_ofNat]
  have hlinear :
      algebraMap K M ((51 : K) / 2) *
          algebraMap K M (1 / 4 : K) =
        algebraMap K M (1 / 64 : K) * (408 : M) := by
    calc
      _ = algebraMap K M (((51 : K) / 2) * (1 / 4 : K)) := by
        rw [← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 408) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (408 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (408 : M) := by
        simp only [map_ofNat]
  have hconst :
      algebraMap K M ((5 : K) / 4) =
        algebraMap K M (1 / 64 : K) * (80 : M) := by
    calc
      _ = algebraMap K M ((1 / 64 : K) * 80) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (80 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (80 : M) := by
        simp only [map_ofNat]
  simp only [descentRootInM, mul_pow]
  linear_combination
    relativeTwoDivisionZ ^ 3 * hcube -
      relativeTwoDivisionZ ^ 2 * hquad +
      relativeTwoDivisionZ * hlinear + hconst +
      algebraMap K M (1 / 64 : K) * relativeTwoDivisionZ_cubic

end

end MazurTorsion.XOneEighteenQuotientTwoDescentModel

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDescentAlgebraEquiv. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Identifying the `X₁(18)` descent algebra with the explicit compositum

The generic `x - T` descent is phrased in the cubic algebra obtained from
the completed two-division polynomial.  The arithmetic certificates use the
explicit relative cubic compositum generated by `s`, with `s³ = 3s + 10`.
This file gives an actual algebra equivalence between those presentations.

The inverse is completely explicit.  If `z` denotes the root of the
completed two-division polynomial, then

`s = (4z² - 11z + 70) / 27`.

Thus no irreducibility or dimension-count oracle is hidden in the bridge.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDescentAlgebraEquiv

noncomputable section

open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The completed two-division root generates the explicit relative cubic
field: the original generator is recovered by this quadratic expression. -/
theorem recover_s_in_compositum :
    (4 * descentRootInM ^ 2 - 11 * descentRootInM + 70) / 27 = s := by
  have hquarter : algebraMap K M (1 / 4 : K) = (1 / 4 : M) := by
    simp only [div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
  simp only [descentRootInM, relativeTwoDivisionZ]
  rw [hquarter]
  field_simp
  linear_combination 9 * (s - 4) * s_cubic

private theorem descentRootInM_adjoin_eq_top :
    IntermediateField.adjoin K {descentRootInM} = ⊤ := by
  let L : IntermediateField K M :=
    IntermediateField.adjoin K {descentRootInM}
  have hz : descentRootInM ∈ L :=
    IntermediateField.mem_adjoin_simple_self K descentRootInM
  have hs : s ∈ L := by
    rw [← recover_s_in_compositum]
    exact L.div_mem
      (L.add_mem
        (L.sub_mem
          (L.mul_mem (L.natCast_mem 4) (L.pow_mem hz 2))
          (L.mul_mem (L.natCast_mem 11) hz))
        (L.natCast_mem 70))
      (L.natCast_mem 27)
  apply top_unique
  intro x _hx
  have hadjoin :
      Algebra.adjoin K ({s} : Set M) ≤
        L.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  have hsTop : Algebra.adjoin K ({s} : Set M) = ⊤ := by
    change Algebra.adjoin K
      ({AdjoinRoot.root relativePolynomial} : Set M) = ⊤
    exact AdjoinRoot.adjoinRoot_eq_top
  rw [hsTop] at hadjoin
  change x ∈ L
  exact hadjoin (show x ∈ (⊤ : Subalgebra K M) from trivial)

/-- The completed two-division cubic is irreducible over the real cubic
coefficient field. -/
theorem descentPolynomial_irreducible :
    Irreducible descentCurve.toAffine.f := by
  have hroot : Polynomial.aeval descentRootInM descentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact descentRootInM_isRoot
  have hdegree : (minpoly K descentRootInM).natDegree = 3 := by
    have h :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        K descentRootInM).mp descentRootInM_adjoin_eq_top
    simpa only [finrank_M_over_K] using h
  have hint : IsIntegral K descentRootInM := IsIntegral.of_finite K descentRootInM
  have hdvd : minpoly K descentRootInM ∣ descentCurve.toAffine.f :=
    minpoly.dvd K descentRootInM hroot
  have heq : descentCurve.toAffine.f = minpoly K descentRootInM :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) descentCurve.toAffine.monic_f hdvd (by
        rw [hdegree, descentCurve.toAffine.natDegree_f])
  rw [heq]
  exact minpoly.irreducible hint

private instance descentPolynomial_irreducibleFact :
    Fact (Irreducible descentCurve.toAffine.f) :=
  ⟨descentPolynomial_irreducible⟩

private theorem descentPolynomial_cleared :
    C (4 : K) * descentCurve.toAffine.f =
      C (4 : K) * X ^ 3 - C (3 : K) * X ^ 2 +
        C (102 : K) * X + C (5 : K) := by
  rw [descentCurve_f, mul_add, mul_add, mul_sub]
  simp only [← mul_assoc, ← C_mul]
  norm_num

/-- The distinguished root in the generic completed two-division algebra. -/
def genericRoot : descentCurve.toAffine.A :=
  AdjoinRoot.root descentCurve.toAffine.f

/-- The generic root satisfies the cleared completed two-division cubic. -/
theorem genericRoot_cubic :
    4 * genericRoot ^ 3 - 3 * genericRoot ^ 2 +
        102 * genericRoot + 5 = 0 := by
  have hroot : Polynomial.aeval genericRoot descentCurve.toAffine.f = 0 := by
    rw [aeval_def]
    exact AdjoinRoot.eval₂_root descentCurve.toAffine.f
  have h := congrArg (Polynomial.aeval genericRoot)
    descentPolynomial_cleared
  simp only [map_mul, map_sub, map_add, map_pow, aeval_X,
    map_ofNat, hroot, mul_zero] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Recover the relative generator from the completed two-division root. -/
def recoveredS : descentCurve.toAffine.A :=
  (4 * genericRoot ^ 2 - 11 * genericRoot + 70) / 27

/-- The recovered element satisfies `S³ - 3S - 10`. -/
theorem recoveredS_cubic : recoveredS ^ 3 = 3 * recoveredS + 10 := by
  have h := genericRoot_cubic
  let N : descentCurve.toAffine.A :=
    4 * genericRoot ^ 2 - 11 * genericRoot + 70
  have hN : N ^ 3 - 3 * 27 ^ 2 * N - 10 * 27 ^ 3 = 0 := by
    dsimp only [N]
    linear_combination
      (16 * genericRoot ^ 3 - 120 * genericRoot ^ 2 +
        705 * genericRoot - 1384) * h
  have h27 : (27 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (27 : K) ≠ 0)
  change (N / 27) ^ 3 = 3 * (N / 27) + 10
  field_simp [h27]
  linear_combination hN

private theorem recoveredS_isRoot :
    Polynomial.aeval recoveredS relativePolynomial = 0 := by
  simp only [relativePolynomial, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination recoveredS_cubic

/-- Map the generic descent algebra to the explicit relative cubic field. -/
def toCompositumHom : descentCurve.toAffine.A →ₐ[K] M :=
  AdjoinRoot.liftAlgHom descentCurve.toAffine.f (Algebra.ofId K M)
    descentRootInM (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      rw [← Polynomial.eval_map_algebraMap]
      exact descentRootInM_isRoot)

@[simp]
theorem toCompositumHom_genericRoot :
    toCompositumHom genericRoot = descentRootInM := by
  exact AdjoinRoot.liftAlgHom_root descentCurve.toAffine.f _ _ _

/-- Map the explicit relative cubic presentation back to the generic
descent algebra. -/
def fromCompositumHom : M →ₐ[K] descentCurve.toAffine.A :=
  AdjoinRoot.liftAlgHom relativePolynomial
    (Algebra.ofId K descentCurve.toAffine.A) recoveredS (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact recoveredS_isRoot)

@[simp]
theorem fromCompositumHom_s : fromCompositumHom s = recoveredS := by
  exact AdjoinRoot.liftAlgHom_root relativePolynomial _ _ _

private theorem recover_genericRoot :
    algebraMap K descentCurve.toAffine.A (1 / 4 : K) *
        (3 * recoveredS ^ 2 - 6 * recoveredS - 5) = genericRoot := by
  have hquarter :
      algebraMap K descentCurve.toAffine.A (1 / 4 : K) =
        (1 / 4 : descentCurve.toAffine.A) := by
    simp only [div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
  rw [hquarter]
  have h := genericRoot_cubic
  let N : descentCurve.toAffine.A :=
    4 * genericRoot ^ 2 - 11 * genericRoot + 70
  have hN :
      3 * N ^ 2 - 6 * 27 * N - 5 * 27 ^ 2 -
          4 * 27 ^ 2 * genericRoot = 0 := by
    dsimp only [N]
    linear_combination 3 * (4 * genericRoot - 19) * h
  have h4 : (4 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (4 : K) ≠ 0)
  have h27 : (27 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (27 : K) ≠ 0)
  change (1 / 4 : descentCurve.toAffine.A) *
      (3 * (N / 27) ^ 2 - 6 * (N / 27) - 5) = genericRoot
  field_simp [h4, h27]
  linear_combination hN

private theorem to_from :
    toCompositumHom.comp fromCompositumHom = AlgHom.id K M := by
  apply AdjoinRoot.algHom_ext
  change toCompositumHom (fromCompositumHom s) = s
  rw [fromCompositumHom_s]
  simpa only [recoveredS, map_div₀, _root_.map_add,
    _root_.map_sub, _root_.map_mul, _root_.map_pow,
    _root_.map_ofNat, toCompositumHom_genericRoot] using
      recover_s_in_compositum

private theorem from_to :
    fromCompositumHom.comp toCompositumHom =
      AlgHom.id K descentCurve.toAffine.A := by
  apply AdjoinRoot.algHom_ext
  change fromCompositumHom (toCompositumHom genericRoot) = genericRoot
  rw [toCompositumHom_genericRoot]
  simpa only [descentRootInM, relativeTwoDivisionZ, map_div₀,
    _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow,
    _root_.map_inv₀, _root_.map_ofNat, fromCompositumHom_s,
    AlgHom.commutes] using recover_genericRoot

/-- The generic `x - T` algebra is the explicit degree-nine compositum,
as an algebra over the real cubic coefficient field. -/
def descentAlgebraEquiv : descentCurve.toAffine.A ≃ₐ[K] M :=
  AlgEquiv.ofAlgHom toCompositumHom fromCompositumHom to_from from_to

@[simp]
theorem descentAlgebraEquiv_genericRoot :
    descentAlgebraEquiv genericRoot = descentRootInM := by
  exact toCompositumHom_genericRoot



end

end MazurTorsion.XOneEighteenDescentAlgebraEquiv

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/























/-! ## Integral generators and their conductors -/

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1

theorem coefficientPolynomialInt_monic : coefficientPolynomialInt.Monic := by
  simp only [coefficientPolynomialInt]
  monicity <;> norm_num



private theorem coefficientPolynomialInt_aeval_tau :
    Polynomial.aeval Q.tau coefficientPolynomialInt = 0 := by
  simp only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one]
  linear_combination Q.tau_cubic

/-- The coefficient-field generator as an algebraic integer. -/
def coefficientInteger : 𝓞 Q.K :=
  ⟨Q.tau, ⟨coefficientPolynomialInt, coefficientPolynomialInt_monic,
    coefficientPolynomialInt_aeval_tau⟩⟩























/-! ## Exact finite-field irreducibility certificates -/

















































/-! ## Kummer--Dedekind and inertia in the compositum -/



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenMinimalTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A dyadic-support two-descent model for the `X₁(18)` quotient

The rational-coefficient model used for explicit two-division arithmetic is
obtained from the original real-cubic quotient by a change with scale `3`.
It is consequently nonminimal at the primes above `3`.  For the global
Selmer containment we instead complete the square directly on the original
quotient, whose discriminant is `-2`.

The abscissas on the two completed-square models are related by

`z = 9 w + 3τ² + 3τ - 8`.

Thus the new cubic algebra is the same explicit degree-nine compositum, but
its bad-prime support is genuinely dyadic.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenMinimalTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenDescentAlgebraEquiv



private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring



/-- Exact coefficients of the minimal completed-square model. -/
theorem minimalDescentCurve_eq :
    minimalDescentCurve =
      (⟨0, tau ^ 2 + tau - (11 : K) / 4, 0,
          (-tau ^ 2 + tau + 7) / 2,
          (2 * tau ^ 2 + tau - 5) / 4⟩ : WeierstrassCurve K) := by
  ext
  all_goals
    norm_num [minimalDescentCurve, quotientCurve,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  all_goals ring_nf
  all_goals simp only [tau_pow_four, tau_cubic]
  all_goals ring

instance minimalDescentCurve_isElliptic : minimalDescentCurve.IsElliptic := by
  dsimp only [minimalDescentCurve]
  infer_instance

instance minimalDescentCurve_isCharNeTwoNF :
    minimalDescentCurve.IsCharNeTwoNF := by
  dsimp only [minimalDescentCurve]
  infer_instance



/-- The monic cubic for the minimal completed-square model. -/
theorem minimalDescentCurve_f :
    minimalDescentCurve.toAffine.f =
      X ^ 3 + C (tau ^ 2 + tau - (11 : K) / 4) * X ^ 2 +
        C ((-tau ^ 2 + tau + 7) / 2) * X +
          C ((2 * tau ^ 2 + tau - 5) / 4) := by
  rw [minimalDescentCurve_eq]

/-- The minimal cubic has discriminant `-1/8`; in particular its only bad
rational support is dyadic. -/
theorem minimalDescentCurve_discr_f :
    minimalDescentCurve.toAffine.f.discr = -(1 : K) / 8 := by
  have hdelta : minimalDescentCurve.Δ = -2 := by
    rw [minimalDescentCurve, WeierstrassCurve.variableChange_Δ,
      quotientCurve_discriminant]
    norm_num [WeierstrassCurve.toCharNeTwoNF]
  rw [minimalDescentCurve.toAffine.Δ_eq_discr_f] at hdelta
  calc
    minimalDescentCurve.toAffine.f.discr =
        (1 / 16 : K) * (16 * minimalDescentCurve.toAffine.f.discr) := by
          field_simp
    _ = (1 / 16 : K) * (-2) := by rw [hdelta]
    _ = -(1 : K) / 8 := by norm_num





/-- The affine root change is reversible. -/
theorem descentRootInM_eq_minimal :
    descentRootInM =
      9 * minimalDescentRootInM +
        algebraMap K M rationalAbscissaTranslation := by
  simp only [minimalDescentRootInM]
  field_simp
  ring

/-- The displayed element is a root of the minimal completed-square cubic. -/
theorem minimalDescentRootInM_isRoot :
    Polynomial.IsRoot
      (minimalDescentCurve.toAffine.f.map (algebraMap K M))
        minimalDescentRootInM := by
  have hz :
      4 * descentRootInM ^ 3 - 3 * descentRootInM ^ 2 +
          102 * descentRootInM + 5 = 0 := by
    have h := congrArg descentAlgebraEquiv genericRoot_cubic
    simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      descentAlgebraEquiv_genericRoot, map_zero] using h
  have ht4 : t ^ 4 = 3 * t ^ 2 + t := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = 3 * t ^ 2 + t := by rw [t_cubic]; ring
  have ht5 : t ^ 5 = t ^ 2 + 9 * t + 3 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = 3 * t ^ 3 + t ^ 2 := by rw [ht4]; ring
      _ = t ^ 2 + 9 * t + 3 := by rw [t_cubic]; ring
  have ht6 : t ^ 6 = 9 * t ^ 2 + 6 * t + 1 := by
    calc
      t ^ 6 = t * t ^ 5 := by ring
      _ = t ^ 3 + 9 * t ^ 2 + 3 * t := by rw [ht5]; ring
      _ = 9 * t ^ 2 + 6 * t + 1 := by rw [t_cubic]; ring
  rw [Polynomial.IsRoot, minimalDescentCurve_f,
    Polynomial.eval_map_algebraMap]
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  simp only [minimalDescentRootInM, rationalAbscissaTranslation,
    map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg,
    map_div₀,
    show algebraMap K M tau = t by rfl]
  field_simp
  ring_nf
  rw [ht6, ht5, ht4, t_cubic]
  ring_nf
  ring_nf at hz
  linear_combination 2 * hz

private theorem minimalDescentRootInM_adjoin_eq_top :
    IntermediateField.adjoin K {minimalDescentRootInM} = ⊤ := by
  let L : IntermediateField K M :=
    IntermediateField.adjoin K {minimalDescentRootInM}
  have hw : minimalDescentRootInM ∈ L :=
    IntermediateField.mem_adjoin_simple_self K minimalDescentRootInM
  have hz : descentRootInM ∈ L := by
    rw [descentRootInM_eq_minimal]
    exact L.add_mem
      (L.mul_mem (L.natCast_mem 9) hw)
      (L.algebraMap_mem rationalAbscissaTranslation)
  have hs : s ∈ L := by
    rw [← recover_s_in_compositum]
    exact L.div_mem
      (L.add_mem
        (L.sub_mem
          (L.mul_mem (L.natCast_mem 4) (L.pow_mem hz 2))
          (L.mul_mem (L.natCast_mem 11) hz))
        (L.natCast_mem 70))
      (L.natCast_mem 27)
  apply top_unique
  intro x _hx
  have hadjoin :
      Algebra.adjoin K ({s} : Set M) ≤ L.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  have hsTop : Algebra.adjoin K ({s} : Set M) = ⊤ := by
    change Algebra.adjoin K
      ({AdjoinRoot.root relativePolynomial} : Set M) = ⊤
    exact AdjoinRoot.adjoinRoot_eq_top
  rw [hsTop] at hadjoin
  exact hadjoin (show x ∈ (⊤ : Subalgebra K M) from trivial)

/-- The minimal completed-square cubic is irreducible over the real cubic
coefficient field. -/
theorem minimalDescentPolynomial_irreducible :
    Irreducible minimalDescentCurve.toAffine.f := by
  have hroot :
      Polynomial.aeval minimalDescentRootInM
        minimalDescentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact minimalDescentRootInM_isRoot
  have hdegree : (minpoly K minimalDescentRootInM).natDegree = 3 := by
    have h :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        K minimalDescentRootInM).mp minimalDescentRootInM_adjoin_eq_top
    simpa only [finrank_M_over_K] using h
  have hint : IsIntegral K minimalDescentRootInM :=
    IsIntegral.of_finite K minimalDescentRootInM
  have hdvd : minpoly K minimalDescentRootInM ∣
      minimalDescentCurve.toAffine.f :=
    minpoly.dvd K minimalDescentRootInM hroot
  have heq : minimalDescentCurve.toAffine.f =
      minpoly K minimalDescentRootInM :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) minimalDescentCurve.toAffine.monic_f hdvd (by
        rw [hdegree, minimalDescentCurve.toAffine.natDegree_f])
  rw [heq]
  exact minpoly.irreducible hint

private instance minimalDescentPolynomial_irreducibleFact :
    Fact (Irreducible minimalDescentCurve.toAffine.f) :=
  ⟨minimalDescentPolynomial_irreducible⟩

/-- The distinguished root in the generic minimal descent algebra. -/
def minimalGenericRoot : minimalDescentCurve.toAffine.A :=
  AdjoinRoot.root minimalDescentCurve.toAffine.f

/-- The canonical map from the generic minimal descent algebra to the
explicit degree-nine compositum. -/
def minimalToCompositumHom : minimalDescentCurve.toAffine.A →ₐ[K] M :=
  AdjoinRoot.liftAlgHom minimalDescentCurve.toAffine.f (Algebra.ofId K M)
    minimalDescentRootInM (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      rw [← Polynomial.eval_map_algebraMap]
      exact minimalDescentRootInM_isRoot)

@[simp]
theorem minimalToCompositumHom_genericRoot :
    minimalToCompositumHom minimalGenericRoot = minimalDescentRootInM := by
  exact AdjoinRoot.liftAlgHom_root minimalDescentCurve.toAffine.f _ _ _

private theorem minimalToCompositumHom_bijective :
    Function.Bijective minimalToCompositumHom := by
  letI : Module.Finite K minimalDescentCurve.toAffine.A :=
    (AdjoinRoot.powerBasis minimalDescentCurve.toAffine.f_ne_zero).finite
  have hinjective : Function.Injective minimalToCompositumHom :=
    minimalToCompositumHom.toRingHom.injective
  have hfinrank :
      Module.finrank K minimalDescentCurve.toAffine.A =
        Module.finrank K M := by
    rw [minimalDescentCurve.toAffine.finrank_A, finrank_M_over_K]
  have hsurjective : Function.Surjective minimalToCompositumHom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := minimalToCompositumHom.toLinearMap) hfinrank).mp hinjective
  exact ⟨hinjective, hsurjective⟩

/-- The minimal dyadic-support descent algebra is the explicit degree-nine
compositum, as a `K`-algebra. -/
def minimalDescentAlgebraEquiv :
    minimalDescentCurve.toAffine.A ≃ₐ[K] M :=
  AlgEquiv.ofBijective minimalToCompositumHom
    minimalToCompositumHom_bijective

@[simp]
theorem minimalDescentAlgebraEquiv_genericRoot :
    minimalDescentAlgebraEquiv minimalGenericRoot =
      minimalDescentRootInM := by
  exact minimalToCompositumHom_genericRoot

/-- The induced equivalence on square classes. -/
def minimalDescentSquareclassEquiv :
    minimalDescentCurve.toAffine.M ≃* Units.modPow M 2 :=
  Units.modPow.congr minimalDescentAlgebraEquiv.toMulEquiv 2

/-- The explicit algebra identification preserves the relative norm. -/
theorem norm_minimalDescentAlgebraEquiv
    (x : minimalDescentCurve.toAffine.A) :
    Algebra.norm K (minimalDescentAlgebraEquiv x) =
      Algebra.norm K x :=
  Algebra.norm_eq_of_algEquiv minimalDescentAlgebraEquiv x

end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Global Selmer bookkeeping for the `X₁(18)` two-descent

This module connects the arithmetic of the explicit degree-nine
two-division field to the generic supported-Selmer cardinality package.
The remaining prime and local-image calculations enter through narrow
certificate hypotheses: the theorem below does not assume a Selmer or
Mordell--Weil conclusion.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenGlobalSelmerBridge

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionExactSignature
open MazurTorsion.XOneEighteenDescentAlgebraEquiv
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes















/-! ## The exact dyadic support -/





/-! ## The minimal model has genuinely dyadic bad support -/

private theorem tau_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K)) :
    MazurTorsion.XOneEighteenRealCubicQuotient.tau ∈
      (v.valuation K).integer := by
  change v.valuation K
      MazurTorsion.XOneEighteenRealCubicQuotient.tau ≤ 1
  have h := v.valuation_le_one (K := K) coefficientInteger
  change v.valuation K (coefficientInteger : K) ≤ 1 at h
  have hcoe : (coefficientInteger : K) =
      MazurTorsion.XOneEighteenRealCubicQuotient.tau := rfl
  rwa [hcoe] at h

private theorem valuation_two_eq_one_of_notMem_coefficientDyadicSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K 2 = 1 := by
  simpa only [coefficientDyadicSupport, Set.mem_setOf_eq, not_not] using hv

private theorem inv_two_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    (2 : K)⁻¹ ∈ (v.valuation K).integer := by
  change v.valuation K (2 : K)⁻¹ ≤ 1
  rw [map_inv₀,
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv]
  simp

private theorem inv_four_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    (4 : K)⁻¹ ∈ (v.valuation K).integer := by
  change v.valuation K (4 : K)⁻¹ ≤ 1
  rw [show (4 : K) = 2 ^ 2 by norm_num, map_inv₀, map_pow,
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv]
  simp

/-- The quadratic coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₂_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₂ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau - (11 : K) / 4 ∈
    (v.valuation K).integer
  exact (v.valuation K).integer.sub_mem
    ((v.valuation K).integer.add_mem
      ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2)
      (tau_mem_valuationInteger v))
    ((v.valuation K).integer.mul_mem (ofNat_mem _ 11)
      (inv_four_mem_valuationInteger v hv))

/-- The linear coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₄_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₄ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change (-MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau + (7 : K)) / 2 ∈
    (v.valuation K).integer
  rw [div_eq_mul_inv]
  exact (v.valuation K).integer.mul_mem
    ((v.valuation K).integer.add_mem
      ((v.valuation K).integer.add_mem
        ((v.valuation K).integer.neg_mem
          ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2))
        (tau_mem_valuationInteger v))
      (ofNat_mem _ 7))
    (inv_two_mem_valuationInteger v hv)

/-- The constant coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₆_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₆ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change (2 * MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau - (5 : K)) / 4 ∈
    (v.valuation K).integer
  rw [div_eq_mul_inv]
  exact (v.valuation K).integer.mul_mem
    ((v.valuation K).integer.sub_mem
      ((v.valuation K).integer.add_mem
        ((v.valuation K).integer.mul_mem
          (ofNat_mem _ 2)
          ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2))
        (tau_mem_valuationInteger v))
      (ofNat_mem _ 5))
    (inv_four_mem_valuationInteger v hv)

/-- The minimal cubic discriminant is a unit away from the dyadic
support. -/
theorem minimalDescentCurve_valuation_discr_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.f.discr = 1 := by
  rw [minimalDescentCurve_discr_f]
  have htwo :=
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv
  rw [show (8 : K) = 2 ^ 3 by norm_num, map_div₀,
    Valuation.map_neg, map_one, map_pow, htwo]
  simp

/-- The generic `x - T` map for the minimal completed-square model has
dyadically supported image.  This is the concrete global containment that
fails for the scale-three rational model. -/
theorem minimalDescentCurve_range_μ_le_dyadicSelmerGroupA :
    (minimalDescentCurve.toAffine.μ).range ≤
      minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport := by
  exact minimalDescentCurve.toAffine.range_μ_le_selmerGroupA
    (𝓞 K) coefficientDyadicSupport
    minimalDescentCurve_valuation_a₂_le_one
    minimalDescentCurve_valuation_a₄_le_one
    minimalDescentCurve_valuation_a₆_le_one
    minimalDescentCurve_valuation_discr_eq_one

/-! ## Relative norm and its four checked kernel generators -/





























private theorem relativeNorm_fieldSquareclass_eq_one
    (x : M) (hx : x ≠ 0) (hsq : IsSquare (Algebra.norm K x)) :
    relativeNormSquareclasses (fieldSquareclass x hx) = 1 := by
  rw [relativeNormSquareclasses, fieldSquareclass,
    Units.modPow.map_mk, Units.modPow.mk_eq_one_iff_isSquare]
  simpa only [Units.coe_map, Units.val_mk0] using hsq

/-- Every explicit generator lies in the relative norm kernel. -/
theorem kernelGenerator_mem (i : Fin 4) :
    kernelGenerator i ∈ relativeNormSquareclasses.ker := by
  rw [MonoidHom.mem_ker]
  fin_cases i
  · exact relativeNorm_fieldSquareclass_eq_one h1 h1_ne_zero
      ⟨1, by simpa using norm_h1⟩
  · exact relativeNorm_fieldSquareclass_eq_one h2 h2_ne_zero
      ⟨1, by simpa using norm_h2⟩
  · exact relativeNorm_fieldSquareclass_eq_one h3 h3_ne_zero
      ⟨2, by rw [norm_h3]; norm_num⟩
  · exact relativeNorm_fieldSquareclass_eq_one h4 h4_ne_zero
      ⟨2 * (Q.tau ^ 2 - 2), by rw [norm_h4_eq_square, pow_two]⟩



/-- Every masked product remains in the relative norm kernel. -/
theorem kernelRepresentative_mem (mask : Fin 16) :
    kernelRepresentative mask ∈ relativeNormSquareclasses.ker := by
  simp only [MonoidHom.mem_ker, kernelRepresentative, map_mul]
  have hgen (i : Fin 4) : relativeNormSquareclasses (kernelGenerator i) = 1 :=
    MonoidHom.mem_ker.mp (kernelGenerator_mem i)
  split_ifs <;> simp [hgen]



/-! ## Cardinality from genuine arithmetic certificates -/







/-! ## The actual ambient relative norm -/



















/-- Every masked product is dyadically supported once the four generators
are. -/
theorem kernelRepresentative_mem_dyadicSelmer
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    kernelRepresentative mask ∈ DyadicSelmerM := by
  simp only [kernelRepresentative]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
    split <;> simp [C.generator_mem]

/-- The sixteen explicit products as elements of the supported relative
norm kernel. -/
def dyadicKernelRepresentative
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    fullDyadicRelativeNorm.ker := by
  refine ⟨⟨kernelRepresentative mask,
    kernelRepresentative_mem_dyadicSelmer C mask⟩, ?_⟩
  change relativeNormSquareclasses (kernelRepresentative mask) =
    (1 : Units.modPow K 2)
  exact MonoidHom.mem_ker.mp (kernelRepresentative_mem mask)

/-- The separately registered unconditional enumeration supplies surjectivity;
the original injectivity assumption supplies injectivity. The original contract
and its arithmetic parameters remain unchanged. -/
theorem dyadicKernelRepresentative_bijective
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (V : DyadicValuationCertificate)
    (C : KernelGeneratorSupportCertificate)
    (hinjective : Function.Injective kernelRepresentative) :
    Function.Bijective (dyadicKernelRepresentative C) := by
  constructor
  · intro a b hab
    apply hinjective
    exact congrArg (fun z : fullDyadicRelativeNorm.ker ↦
      ((z : DyadicSelmerM) : Units.modPow M 2)) hab
  · intro z
    obtain ⟨mask, hmask⟩ := MazurTransfer.order18_original_global_norm_kernel_enumeration z
    refine ⟨mask, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hmask


/-! ## The global subgroup consumed by the Selmer sieve -/

/-- On the minimal generic descent algebra, the global dyadic norm kernel
is the intersection of dyadic support (transported through the explicit
algebra equivalence) and the generic relative-norm kernel. -/
def descentDyadicNormKernel : Subgroup minimalDescentCurve.toAffine.M :=
  DyadicSelmerM.comap minimalDescentSquareclassEquiv.toMonoidHom ⊓
    minimalDescentCurve.toAffine.normM.ker



/-! ## The unique generic descent factor -/

local instance minimalDescentFactorsUnique :
    Unique minimalDescentCurve.toAffine.f.Factors :=
  Polynomial.Factors.unique minimalDescentPolynomial_irreducible
    minimalDescentCurve.toAffine.monic_f

/-- For the irreducible two-division polynomial, the product decomposition
of squareclasses has only its distinguished field factor. -/
def singleFactorSquareclassEquiv :
    minimalDescentCurve.toAffine.M ≃*
      Units.modPow (AdjoinRoot
        ((default : minimalDescentCurve.toAffine.f.Factors) : K[X])) 2 :=
  (AdjoinRoot.modPowEquivPiFactors minimalDescentCurve.toAffine.f_ne_zero
    minimalDescentCurve.toAffine.squarefree_f 2).trans
      (MulEquiv.piUnique fun p : minimalDescentCurve.toAffine.f.Factors ↦
        Units.modPow (AdjoinRoot (p : K[X])) 2)

private theorem projFactor_default_eq_id :
    AdjoinRoot.projFactor minimalDescentCurve.toAffine.f_ne_zero
        minimalDescentCurve.toAffine.squarefree_f default =
      RingHom.id minimalDescentCurve.toAffine.A := by
  apply AdjoinRoot.ringHom_ext <;> rfl

/-- Evaluating the unique-factor product decomposition at its sole factor
is the identity squareclass map. -/
theorem singleFactorSquareclassEquiv_eq_refl :
    singleFactorSquareclassEquiv =
      MulEquiv.refl minimalDescentCurve.toAffine.M := by
  apply MulEquiv.ext
  intro m
  induction m using QuotientGroup.induction_on with
  | H u =>
      change
        AdjoinRoot.modPowEquivPiFactors minimalDescentCurve.toAffine.f_ne_zero
            minimalDescentCurve.toAffine.squarefree_f 2 (QuotientGroup.mk u) default =
          QuotientGroup.mk u
      rw [AdjoinRoot.modPowEquivPiFactors_mk, projFactor_default_eq_id]
      rfl

/-- The explicit algebra equivalence commutes with the relative norm on
squareclasses. -/
theorem relativeNorm_minimalDescentSquareclassEquiv
    (m : minimalDescentCurve.toAffine.M) :
    relativeNormSquareclasses (minimalDescentSquareclassEquiv m) =
      minimalDescentCurve.toAffine.normM m := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply, relativeNormSquareclasses,
    minimalDescentSquareclassEquiv]
  exact congrArg QuotientGroup.mk <| Units.ext <|
    norm_minimalDescentAlgebraEquiv (u : minimalDescentCurve.toAffine.A)

/-! ## Integral-closure transport for the unique factor -/

private abbrev MinimalFactorField :=
  AdjoinRoot
    ((default : minimalDescentCurve.toAffine.f.Factors) : K[X])

private abbrev MinimalFactorIntegers :=
  minimalDescentCurve.toAffine.ringOfIntegersFactor (𝓞 K) default

private theorem minimalDescentAlgebraEquiv_comp_base :
    (algebraMap (𝓞 K) M).comp (RingHom.id (𝓞 K)) =
      minimalDescentAlgebraEquiv.toRingEquiv.toRingHom.comp
        (algebraMap (𝓞 K) minimalDescentCurve.toAffine.A) := by
  ext x
  change algebraMap K M (algebraMap (𝓞 K) K x) =
    minimalDescentAlgebraEquiv
      (algebraMap K minimalDescentCurve.toAffine.A
        (algebraMap (𝓞 K) K x))
  rw [minimalDescentAlgebraEquiv.commutes]

private theorem minimalDescentAlgebraEquiv_symm_comp_base :
    (algebraMap (𝓞 K) minimalDescentCurve.toAffine.A).comp
        (RingHom.id (𝓞 K)) =
      minimalDescentAlgebraEquiv.symm.toRingEquiv.toRingHom.comp
        (algebraMap (𝓞 K) M) := by
  ext x
  change algebraMap K minimalDescentCurve.toAffine.A
      (algebraMap (𝓞 K) K x) =
    minimalDescentAlgebraEquiv.symm
      (algebraMap K M (algebraMap (𝓞 K) K x))
  rw [minimalDescentAlgebraEquiv.symm.commutes]

/-- The algebra equivalence restricts to the corresponding integral
closures over the coefficient ring. -/
private def minimalFactorIntegersEquiv :
    MinimalFactorIntegers ≃+* RelativeIntegers where
  toFun x := ⟨minimalDescentAlgebraEquiv x,
    IsIntegral.map_of_comp_eq (RingHom.id (𝓞 K))
      minimalDescentAlgebraEquiv.toRingEquiv.toRingHom
      minimalDescentAlgebraEquiv_comp_base x.property⟩
  invFun x := ⟨minimalDescentAlgebraEquiv.symm x,
    IsIntegral.map_of_comp_eq (RingHom.id (𝓞 K))
      minimalDescentAlgebraEquiv.symm.toRingEquiv.toRingHom
      minimalDescentAlgebraEquiv_symm_comp_base x.property⟩
  left_inv x :=
    Subtype.ext (minimalDescentAlgebraEquiv.symm_apply_apply x)
  right_inv x :=
    Subtype.ext (minimalDescentAlgebraEquiv.apply_symm_apply x)
  map_mul' x y := Subtype.ext
    (map_mul minimalDescentAlgebraEquiv
      (x : minimalDescentCurve.toAffine.A)
      (y : minimalDescentCurve.toAffine.A))
  map_add' x y := Subtype.ext
    (map_add minimalDescentAlgebraEquiv
      (x : minimalDescentCurve.toAffine.A)
      (y : minimalDescentCurve.toAffine.A))

/-- The same field equivalence with the unique factor exposed in its
source type. -/
private def minimalFactorToCompositumEquiv :
    MinimalFactorField ≃+* M :=
  minimalDescentAlgebraEquiv.toRingEquiv

private theorem minimalFactor_field_comp :
    (algebraMap RelativeIntegers M).comp
        minimalFactorIntegersEquiv.toRingHom =
      minimalFactorToCompositumEquiv.toRingHom.comp
        (algebraMap MinimalFactorIntegers MinimalFactorField) := by
  ext x
  rfl

private theorem minimalFactorIntegersEquiv_algebraMap (x : 𝓞 K) :
    minimalFactorIntegersEquiv
        (algebraMap (𝓞 K) MinimalFactorIntegers x) =
      algebraMap (𝓞 K) RelativeIntegers x := by
  apply Subtype.ext
  change minimalDescentAlgebraEquiv
      (algebraMap K minimalDescentCurve.toAffine.A
        (algebraMap (𝓞 K) K x)) =
    algebraMap K M (algebraMap (𝓞 K) K x)
  exact minimalDescentAlgebraEquiv.commutes _

private theorem minimalFactorIntegersEquiv_comp_base :
    minimalFactorIntegersEquiv.toRingHom.comp
        (algebraMap (𝓞 K) MinimalFactorIntegers) =
      algebraMap (𝓞 K) RelativeIntegers := by
  ext x
  exact congrArg Subtype.val
    (minimalFactorIntegersEquiv_algebraMap x)

private theorem below_comap_minimalFactorIntegersEquiv
    (w : HeightOneSpectrum RelativeIntegers)
    (hne : w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom ≠ ⊥) :
    (HeightOneSpectrum.comapOfNeBot
        minimalFactorIntegersEquiv.toRingHom w hne).below (𝓞 K) =
      w.below (𝓞 K) := by
  apply HeightOneSpectrum.ext
  change
    (w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom).comap
        (algebraMap (𝓞 K) MinimalFactorIntegers) =
      w.asIdeal.comap (algebraMap (𝓞 K) RelativeIntegers)
  rw [Ideal.comap_comap, minimalFactorIntegersEquiv_comp_base]

private theorem minimalDescentSquareclassEquiv_eq_factorMap
    (m : Units.modPow MinimalFactorField 2) :
    minimalDescentSquareclassEquiv m =
      Units.modPow.map minimalFactorToCompositumEquiv.toMonoidHom 2 m := by
  induction m using QuotientGroup.induction_on with
  | H u => rfl

/-- Valuation support transports from the unique generic factor to the
explicit degree-nine field through the integral-closure equivalence. -/
private theorem minimalFactorSelmer_mem_dyadicSelmerM
    (m : Units.modPow MinimalFactorField 2)
    (hm : m ∈ minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
      coefficientDyadicSupport default) :
    minimalDescentSquareclassEquiv m ∈ DyadicSelmerM := by
  induction m using QuotientGroup.induction_on with
  | H u =>
      intro w hw
      rw [minimalDescentSquareclassEquiv_eq_factorMap,
        Units.modPow.map_mk,
        HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      have hne :
          w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom ≠ ⊥ := by
        intro hbot
        apply w.ne_bot
        rw [← Ideal.map_comap_of_surjective
          minimalFactorIntegersEquiv.toRingHom
          minimalFactorIntegersEquiv.surjective w.asIdeal,
          hbot, Ideal.map_bot]
      let v : HeightOneSpectrum MinimalFactorIntegers :=
        HeightOneSpectrum.comapOfNeBot
          minimalFactorIntegersEquiv.toRingHom w hne
      have hv : v ∉ HeightOneSpectrum.primesAbove (𝓞 K)
          MinimalFactorIntegers coefficientDyadicSupport := by
        rw [HeightOneSpectrum.mem_primesAbove_iff]
        rw [show v.below (𝓞 K) = w.below (𝓞 K) from
          below_comap_minimalFactorIntegersEquiv w hne]
        intro hwbelow
        apply hw
        exact (HeightOneSpectrum.mem_primesAbove_iff
          (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hwbelow
      exact HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
        minimalFactorToCompositumEquiv.toRingHom
        minimalFactorIntegersEquiv.toRingHom minimalFactor_field_comp
        w hne u
        ((HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v 2 u).mp
          (hm v hv))

/-- The generic `selmerGroupA` is membership in its unique irreducible
factor, with no residual product condition. -/
theorem mem_selmerGroupA_iff_singleFactor
    (m : minimalDescentCurve.toAffine.M) :
    m ∈ minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport ↔
      singleFactorSquareclassEquiv m ∈
        minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
          coefficientDyadicSupport default := by
  rw [minimalDescentCurve.toAffine.mem_selmerGroupA_iff]
  constructor
  · intro h
    exact h default
  · intro h p
    have hp : p = default := Subsingleton.elim _ _
    subst p
    exact h

/-- The generic supported group embeds in the explicit dyadic supported
squareclasses under the minimal descent-algebra equivalence. -/
theorem minimalDescentCurve_selmerGroupA_le_dyadicSelmerM :
    minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport ≤
      DyadicSelmerM.comap minimalDescentSquareclassEquiv.toMonoidHom := by
  intro m hm
  have hfactor :
      singleFactorSquareclassEquiv m ∈
        minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
          coefficientDyadicSupport default :=
    (mem_selmerGroupA_iff_singleFactor m).mp hm
  rw [singleFactorSquareclassEquiv_eq_refl] at hfactor
  exact minimalFactorSelmer_mem_dyadicSelmerM m hfactor

/-- Every global `x - T` descent class belongs to the explicit dyadic
relative-norm kernel. -/
theorem minimalDescentCurve_range_μ_le_descentDyadicNormKernel :
    (minimalDescentCurve.toAffine.μ).range ≤
      descentDyadicNormKernel := by
  intro m hm
  constructor
  · exact minimalDescentCurve_selmerGroupA_le_dyadicSelmerM
      (minimalDescentCurve_range_μ_le_dyadicSelmerGroupA hm)
  · exact minimalDescentCurve.toAffine.range_μ_le_ker_normM hm

end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenGlobalKernelEquivalence. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The explicit and generic global norm kernels agree

The minimal two-descent algebra is explicitly equivalent to the degree-nine
two-division field.  This file restricts the induced squareclass equivalence
to the dyadically supported relative-norm kernels on the two sides.
-/

namespace MazurTorsion.XOneEighteenGlobalKernelEquivalence

noncomputable section

open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

private def descentDyadicSupportedHom :
    descentDyadicNormKernel →* DyadicSelmerM :=
  (minimalDescentSquareclassEquiv.toMonoidHom.comp
      descentDyadicNormKernel.subtype).codRestrict
    DyadicSelmerM fun x ↦ x.property.1

/-- The explicit squareclass equivalence, restricted from the generic global
dyadic norm kernel to the supported relative-norm kernel. -/
def descentDyadicNormKernelHom :
    descentDyadicNormKernel →* fullDyadicRelativeNorm.ker :=
  descentDyadicSupportedHom.codRestrict fullDyadicRelativeNorm.ker fun x ↦ by
    change relativeNormSquareclasses
      (minimalDescentSquareclassEquiv
        (x : minimalDescentCurve.toAffine.M)) = 1
    rw [relativeNorm_minimalDescentSquareclassEquiv]
    exact x.property.2

/-- The restricted hom has the expected underlying explicit squareclass. -/
@[simp] theorem descentDyadicNormKernelHom_coe
    (x : descentDyadicNormKernel) :
    (((descentDyadicNormKernelHom x : fullDyadicRelativeNorm.ker) :
        DyadicSelmerM) : Units.modPow M 2) =
      minimalDescentSquareclassEquiv x :=
  rfl

private theorem symm_mem_descentDyadicNormKernel
    (y : fullDyadicRelativeNorm.ker) :
    minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2) ∈
      descentDyadicNormKernel := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · apply Subgroup.mem_comap.mpr
    change minimalDescentSquareclassEquiv
      (minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2)) ∈ DyadicSelmerM
    rw [minimalDescentSquareclassEquiv.apply_symm_apply]
    exact y.1.property
  · apply MonoidHom.mem_ker.mpr
    rw [← relativeNorm_minimalDescentSquareclassEquiv,
      minimalDescentSquareclassEquiv.apply_symm_apply]
    have hy := MonoidHom.mem_ker.mp y.property
    change relativeNormSquareclasses
      ((y.1 : DyadicSelmerM) : Units.modPow M 2) = 1 at hy
    exact hy

/-- The restricted hom is a bijection.  Surjectivity is witnessed explicitly
by the inverse squareclass equivalence. -/
theorem descentDyadicNormKernelHom_bijective :
    Function.Bijective descentDyadicNormKernelHom := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply minimalDescentSquareclassEquiv.injective
    have h := congrArg
      (fun z : fullDyadicRelativeNorm.ker ↦
        ((z.1 : DyadicSelmerM) : Units.modPow M 2)) hxy
    simpa only [descentDyadicNormKernelHom_coe] using h
  · intro y
    let x : descentDyadicNormKernel :=
      ⟨minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2),
          symm_mem_descentDyadicNormKernel y⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    calc
      (((descentDyadicNormKernelHom x : fullDyadicRelativeNorm.ker) :
          DyadicSelmerM) : Units.modPow M 2) =
          minimalDescentSquareclassEquiv x :=
        descentDyadicNormKernelHom_coe x
      _ = minimalDescentSquareclassEquiv
          (minimalDescentSquareclassEquiv.symm
            ((y.1 : DyadicSelmerM) : Units.modPow M 2)) := rfl
      _ = ((y.1 : DyadicSelmerM) : Units.modPow M 2) :=
        minimalDescentSquareclassEquiv.apply_symm_apply _

end

end MazurTorsion.XOneEighteenGlobalKernelEquivalence

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenFinalUnconditional. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Unconditional completion of the `X₁(18)` two-descent

The global dyadic norm kernel has exactly the sixteen explicitly displayed
representatives.  The selected dyadic factor admits only their identity
representative in the local descent image.  Transporting the representatives
back through the checked equivalence with the generic minimal descent algebra
therefore makes the global `x - T` image trivial.

The rank-zero, finite-reduction, and Kubert consumers then give both the full
rational-point classification required by `Challenge.XOneEighteenNoncusp` and
the genuine exact-order-eighteen exclusion.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDescent

noncomputable section

open MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenDyadicKernelSeparation
open MazurTorsion.XOneEighteenDyadicValuationCertificate
open MazurTorsion.XOneEighteenGlobalKernelEquivalence
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenKernelGeneratorSupport
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenFinalRankZero
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumberOne



/-- The checked equivalence between the generic minimal-model norm kernel
and the explicit dyadically supported relative-norm kernel. -/
private def descentDyadicNormKernelEquiv :
    descentDyadicNormKernel ≃* fullDyadicRelativeNorm.ker :=
  MulEquiv.ofBijective descentDyadicNormKernelHom
    descentDyadicNormKernelHom_bijective

/-- The sixteen explicit relative-norm-kernel representatives, transported
back to the generic squareclass algebra of the minimal descent model. -/
private def minimalKernelRepresentative (mask : Fin 16) :
    descentDyadicNormKernel :=
  descentDyadicNormKernelEquiv.symm
    (dyadicKernelRepresentative concreteKernelSupportCertificate mask)

private theorem descentDyadicNormKernelHom_minimalKernelRepresentative
    (mask : Fin 16) :
    descentDyadicNormKernelHom (minimalKernelRepresentative mask) =
      dyadicKernelRepresentative concreteKernelSupportCertificate mask := by
  change descentDyadicNormKernelEquiv
      (descentDyadicNormKernelEquiv.symm
        (dyadicKernelRepresentative concreteKernelSupportCertificate mask)) =
    dyadicKernelRepresentative concreteKernelSupportCertificate mask
  exact descentDyadicNormKernelEquiv.apply_symm_apply _

/-- Under the explicit squareclass equivalence, the transported generic
representative is the corresponding masked product. -/
private theorem minimalKernelRepresentative_squareclass (mask : Fin 16) :
    minimalDescentSquareclassEquiv
        (minimalKernelRepresentative mask : minimalDescentCurve.toAffine.M) =
      kernelRepresentative mask := by
  have h := congrArg
    (fun z : fullDyadicRelativeNorm.ker ↦
      ((z.1 : DyadicSelmerM) : Units.modPow M 2))
    (descentDyadicNormKernelHom_minimalKernelRepresentative mask)
  simpa only [descentDyadicNormKernelHom_coe,
    dyadicKernelRepresentative] using h

/-- The transported representatives exhaust the generic global kernel. -/
private theorem minimalKernelRepresentative_bijective :
    Function.Bijective minimalKernelRepresentative := by
  change Function.Bijective
    (fun mask : Fin 16 ↦ descentDyadicNormKernelEquiv.symm
      (dyadicKernelRepresentative concreteKernelSupportCertificate mask))
  exact descentDyadicNormKernelEquiv.symm.bijective.comp
    (dyadicKernelRepresentative_bijective
      compositumRingOfIntegers_isPrincipal
      dyadicValuationCertificate
      concreteKernelSupportCertificate
      kernelRepresentative_injective)















end

end MazurTorsion.XOneEighteenDescent

end

open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open WeierstrassCurve.Affine

private theorem point_compositum_squareclass_eq (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM ≠ 0) :
    minimalDescentSquareclassEquiv
      (WeierstrassCurve.Affine.μ (W := minimalDescentCurve.toAffine)
        (.ofAdd (.some x y h))) =
      fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv := by
  have hx : minimalDescentCurve.toAffine.f.eval x ≠ 0 :=
    minimalDescentPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
      (by rw [minimalDescentCurve.toAffine.natDegree_f]; norm_num)
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx]
  change (QuotientGroup.mk
    (Units.mapEquiv minimalDescentAlgebraEquiv.toMulEquiv
      ((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit)) : Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2) =
      QuotientGroup.mk (Units.mk0 (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv)
  apply congrArg (fun u : MazurTorsion.XOneEighteenTwoDivisionArithmetic.Mˣ => (QuotientGroup.mk u : Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2))
  apply Units.ext
  change minimalDescentAlgebraEquiv
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit) : minimalDescentCurve.toAffine.A) = _
  rw [IsUnit.unit_spec, map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
  change minimalDescentAlgebraEquiv
    (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K minimalDescentCurve.toAffine.A x) -
      minimalDescentAlgebraEquiv minimalGenericRoot = _
  rw [minimalDescentAlgebraEquiv.commutes, minimalDescentAlgebraEquiv_genericRoot]
  simp only [Units.val_mk0]

open MazurTorsion.XOneEighteenDescent

theorem solution (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM ≠ 0) :
    ∃ mask : Fin 16,
      fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv =
        kernelRepresentative mask := by
  let P : minimalDescentCurve.toAffine.Point := .some x y h
  have hg : WeierstrassCurve.Affine.μ (.ofAdd P) ∈ descentDyadicNormKernel :=
    minimalDescentCurve_range_μ_le_descentDyadicNormKernel ⟨.ofAdd P, rfl⟩
  obtain ⟨mask, hm⟩ := minimalKernelRepresentative_bijective.surjective
    ⟨WeierstrassCurve.Affine.μ (.ofAdd P), hg⟩
  have heq : (minimalKernelRepresentative mask : minimalDescentCurve.toAffine.M) =
      WeierstrassCurve.Affine.μ (.ofAdd P) :=
    congrArg (fun z : descentDyadicNormKernel =>
      (z : minimalDescentCurve.toAffine.M)) hm
  refine ⟨mask, ?_⟩
  rw [← point_compositum_squareclass_eq x y h hv]
  change minimalDescentSquareclassEquiv (WeierstrassCurve.Affine.μ (.ofAdd P)) = _
  rw [← heq]
  exact minimalKernelRepresentative_squareclass mask
#print axioms solution
