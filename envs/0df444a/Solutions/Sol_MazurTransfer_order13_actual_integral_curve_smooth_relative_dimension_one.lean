-- Prove2me | solution 1 for MazurTransfer.order13_actual_integral_curve_smooth_relative_dimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T02:54:52.129401+00:00
-- url     : https://prove2.me/submissions/a5c19d97-5032-47e2-b199-090b4e0b245c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: constructed smoothness of relative dimension exactly one
for the actual integral curve, over every commutative base with 104 a unit.
Named downstream consumer: integral Picard representability and torsion
specialization. Explicit differential and domain proofs are included;
whole-curve base change, geometric integrality and smoothness are accepted
public dependencies. No dimension, rank, model or Picard input is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
import Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

namespace IntegralRelativeDimensionPublicProof

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)

abbrev equation : Polynomial R := X ^ 2 - C f

def powerBasis : PowerBasis R (AdjoinRoot (equation R f)) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f (by decide))

theorem powerBasis_dim : (powerBasis R f).dim = 2 := by
  change (X ^ 2 - C f).natDegree = 2
  exact Polynomial.natDegree_X_pow_sub_C

def basis : Basis (Fin 2) R (AdjoinRoot (equation R f)) :=
  (powerBasis R f).basis.reindex (finCongr (powerBasis_dim R f))

theorem basis_zero : basis R f 0 = 1 := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 0).val :=
      (powerBasis R f).basis_eq_pow _
    _ = 1 := by simp

theorem basis_one : basis R f 1 = AdjoinRoot.root (equation R f) := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 1).val :=
      (powerBasis R f).basis_eq_pow _
    _ = (powerBasis R f).gen := by simp
    _ = AdjoinRoot.root (equation R f) := rfl

def coordinates : AdjoinRoot (equation R f) ≃ₗ[R] R × R :=
  (basis R f).equivFun.trans (LinearEquiv.finTwoArrow R R)

theorem coordinates_symm (v : R × R) :
    (coordinates R f).symm v = AdjoinRoot.of (equation R f) v.1 +
      AdjoinRoot.of (equation R f) v.2 * AdjoinRoot.root (equation R f) := by
  rw [coordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem coordinates_of_add_of_mul_root (a b : R) :
    coordinates R f (AdjoinRoot.of (equation R f) a +
      AdjoinRoot.of (equation R f) b * AdjoinRoot.root (equation R f)) = (a, b) := by
  rw [← coordinates_symm R f (a, b), LinearEquiv.apply_symm_apply]

end MazurTransfer.QuadraticCoordinates

#print axioms MazurTransfer.QuadraticCoordinates.coordinates_symm

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual Kaehler differential module of the quadratic
hyperelliptic coordinate algebra. Named downstream consumer: smoothness of
relative dimension one for the actual order-thirteen chart morphisms.
Adapted completely from the checked owned differential proof, with a
commutative base ring, explicit polynomial Bezout data and a unit 2.
No field, domain, genus or Jacobian assertion is assumed.
-/

noncomputable section
namespace MazurTransfer.IntegralHyperellipticCoordinateDifferentials
open Polynomial Module
variable (K : Type*) [CommRing K] (f : Polynomial K)

abbrev equation : Polynomial (Polynomial K) := X ^ 2 - C f
abbrev CoordinateRing := AdjoinRoot (equation K f)
def x : CoordinateRing K f := AdjoinRoot.of (equation K f) X
def y : CoordinateRing K f := AdjoinRoot.root (equation K f)
abbrev of : Polynomial K →+* CoordinateRing K f := AdjoinRoot.of (equation K f)

theorem y_sq : y K f ^ 2 = of K f f := by
  have h := AdjoinRoot.eval₂_root (equation K f)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem of_eq_aeval (p : Polynomial K) : of K f p = aeval (x K f) p := by
  have h : AdjoinRoot.ofAlgHom K (equation K f) = aeval (x K f) := by
    apply Polynomial.algHom_ext
    simp [x]
  exact DFunLike.congr_fun h p

abbrev Dual := TrivSqZeroExt (CoordinateRing K f) (CoordinateRing K f)

theorem aeval_dual (p : Polynomial K) (a da : CoordinateRing K f) :
    aeval (TrivSqZeroExt.inl a + TrivSqZeroExt.inr da : Dual K f) p =
      TrivSqZeroExt.inl (aeval a p) + TrivSqZeroExt.inr (aeval a p.derivative * da) := by
  have hsq : (TrivSqZeroExt.inr da : Dual K f) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have hmap : (TrivSqZeroExt.inlAlgHom K (CoordinateRing K f) (CoordinateRing K f)).comp
      (aeval a) = aeval (TrivSqZeroExt.inl a : Dual K f) := by
    apply Polynomial.algHom_ext
    simp
  rw [aeval_add_of_sq_eq_zero p _ _ hsq]
  rw [← DFunLike.congr_fun hmap p, ← DFunLike.congr_fun hmap p.derivative]
  change TrivSqZeroExt.inl (aeval a p) +
    TrivSqZeroExt.inl (aeval a p.derivative) * TrivSqZeroExt.inr da = _
  rw [TrivSqZeroExt.inl_mul_inr]
  rfl

def dualX : Dual K f := TrivSqZeroExt.inl (x K f) + TrivSqZeroExt.inr (2 * y K f)
def dualY : Dual K f := TrivSqZeroExt.inl (y K f) + TrivSqZeroExt.inr (of K f f.derivative)

theorem dual_relation : dualY K f ^ 2 = aeval (dualX K f) f := by
  rw [dualX, aeval_dual]
  apply TrivSqZeroExt.ext
  · simp [dualY, pow_two, ← of_eq_aeval, ← y_sq]
  · simp only [dualY, pow_two, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      ← of_eq_aeval, smul_eq_mul, op_smul_eq_smul]
    ring

def dualSection : CoordinateRing K f →ₐ[K] Dual K f :=
  AdjoinRoot.liftAlgHom (equation K f) (aeval (dualX K f)) (dualY K f) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr (dual_relation K f))

@[simp] theorem dualSection_x : dualSection K f (x K f) = dualX K f := by
  simp [dualSection, x]

@[simp] theorem dualSection_y : dualSection K f (y K f) = dualY K f := by
  simp [dualSection, y]

theorem dualSection_fst :
    (TrivSqZeroExt.fstHom K (CoordinateRing K f) (CoordinateRing K f)).comp
      (dualSection K f) = AlgHom.id K (CoordinateRing K f) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change (dualSection K f (x K f)).fst = x K f
    rw [dualSection_x]
    simp [dualX]
  · change (dualSection K f (y K f)).fst = y K f
    rw [dualSection_y]
    simp [dualY]

def tangentDerivation : Derivation K (CoordinateRing K f) (CoordinateRing K f) where
  toLinearMap := ((TrivSqZeroExt.sndHom (CoordinateRing K f) (CoordinateRing K f)).restrictScalars K).comp
    (dualSection K f).toLinearMap
  map_one_eq_zero' := by
    change (dualSection K f 1).snd = 0
    simp
  leibniz' a b := by
    change (dualSection K f (a * b)).snd =
      a • (dualSection K f b).snd + b • (dualSection K f a).snd
    have ha : (dualSection K f a).fst = a := DFunLike.congr_fun (dualSection_fst K f) a
    have hb : (dualSection K f b).fst = b := DFunLike.congr_fun (dualSection_fst K f) b
    rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb]
    simp [smul_eq_mul, mul_comm]

@[simp] theorem tangentDerivation_x : tangentDerivation K f (x K f) = 2 * y K f := by
  change (dualSection K f (x K f)).snd = _
  rw [dualSection_x]
  simp [dualX]

@[simp] theorem tangentDerivation_y : tangentDerivation K f (y K f) = of K f f.derivative := by
  change (dualSection K f (y K f)).snd = _
  rw [dualSection_y]
  simp [dualY]

theorem derivation_of {M : Type*} [AddCommGroup M] [Module (CoordinateRing K f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K f) M]
    (d : Derivation K (CoordinateRing K f) M) (p : Polynomial K) :
    d (of K f p) = of K f p.derivative • d (x K f) := by
  rw [of_eq_aeval, d.map_aeval, ← of_eq_aeval]

theorem derivation_relation {M : Type*} [AddCommGroup M] [Module (CoordinateRing K f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K f) M]
    (d : Derivation K (CoordinateRing K f) M) :
    (2 * y K f) • d (y K f) = of K f f.derivative • d (x K f) := by
  have h := congrArg d (y_sq K f)
  rw [pow_two, d.leibniz, derivation_of] at h
  simpa only [two_mul, add_smul] using h

theorem kaehler_equiv [Nontrivial K] (hf : IsCoprime f f.derivative) (h2 : IsUnit (2 : K)) :
    Nonempty (Ω[CoordinateRing K f⁄K] ≃ₗ[CoordinateRing K f] CoordinateRing K f) := by
  obtain ⟨a, b, hab⟩ := hf
  let A := CoordinateRing K f
  let d := KaehlerDifferential.D K A
  obtain ⟨u, hu⟩ := h2
  have hinv : (2 : K) * ↑(u⁻¹) = 1 := by
    rw [← hu]
    simp
  let c : A := algebraMap K A ↑(u⁻¹)
  have hc : (2 : A) * c = 1 := by
    calc
      _ = algebraMap K A ((2 : K) * ↑(u⁻¹)) := by simp only [c, map_mul, map_ofNat]
      _ = 1 := by rw [hinv, map_one]
  let w : Ω[A⁄K] := (of K f a * y K f * c) • d (x K f) + of K f b • d (y K f)
  have hcoef : of K f a * y K f ^ 2 + of K f b * of K f f.derivative = 1 := by
    rw [y_sq]
    exact (by simpa only [map_add, map_mul, map_one] using congrArg (of K f) hab)
  have hcoeffirst : (2 * y K f) * (of K f a * y K f * c) = of K f a * y K f ^ 2 := by
    calc
      _ = (of K f a * y K f ^ 2) * (2 * c) := by ring
      _ = _ := by rw [hc, mul_one]
  have hrel := derivation_relation K f d
  have hx : (2 * y K f) • w = d (x K f) := by
    calc
      _ = ((2 * y K f) * (of K f a * y K f * c)) • d (x K f) +
          of K f b • ((2 * y K f) • d (y K f)) := by
        dsimp only [w]
        rw [smul_add, smul_smul, smul_comm (2 * y K f) (of K f b)]
      _ = (of K f a * y K f ^ 2) • d (x K f) +
          (of K f b * of K f f.derivative) • d (x K f) := by
        rw [hcoeffirst, hrel, smul_smul]
      _ = _ := by rw [← add_smul, hcoef, one_smul]
  have hy : of K f f.derivative • w = d (y K f) := by
    calc
      _ = (of K f a * y K f * c) • (of K f f.derivative • d (x K f)) +
          (of K f b * of K f f.derivative) • d (y K f) := by
        dsimp only [w]
        simp only [smul_add, smul_smul]
        rw [mul_comm (of K f f.derivative) (of K f a * y K f * c),
          mul_comm (of K f f.derivative) (of K f b)]
      _ = (of K f a * y K f ^ 2) • d (y K f) +
          (of K f b * of K f f.derivative) • d (y K f) := by
        rw [← hrel, smul_smul, mul_comm (of K f a * y K f * c) (2 * y K f), hcoeffirst]
      _ = _ := by rw [← add_smul, hcoef, one_smul]
  let W := Submodule.span A ({w} : Set Ω[A⁄K])
  have hw : w ∈ W := Submodule.subset_span (Set.mem_singleton w)
  have hdx : d (x K f) ∈ W := hx ▸ W.smul_mem (2 * y K f) hw
  have hdy : d (y K f) ∈ W := hy ▸ W.smul_mem (of K f f.derivative) hw
  have hspan : W = ⊤ := by
    apply top_unique
    rw [← KaehlerDifferential.span_range_derivation K A]
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    let p := QuadraticCoordinates.coordinates (Polynomial K) f z
    have hz : z = of K f p.1 + of K f p.2 * y K f := by
      calc
        _ = (QuadraticCoordinates.coordinates (Polynomial K) f).symm p :=
          ((QuadraticCoordinates.coordinates (Polynomial K) f).symm_apply_apply z).symm
        _ = _ := QuadraticCoordinates.coordinates_symm (Polynomial K) f p
    rw [hz, d.map_add, d.leibniz, derivation_of, derivation_of]
    exact W.add_mem (W.smul_mem _ hdx)
      (W.add_mem (W.smul_mem _ hdy) (W.smul_mem _ (W.smul_mem _ hdx)))
  let l : Ω[A⁄K] →ₗ[A] A := (tangentDerivation K f).liftKaehlerDifferential
  have hl : l w = 1 := by
    change (tangentDerivation K f).liftKaehlerDifferential
      ((of K f a * y K f * c) • KaehlerDifferential.D K A (x K f) +
        of K f b • KaehlerDifferential.D K A (y K f)) = 1
    rw [map_add, map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, tangentDerivation_x, tangentDerivation_y]
    simp only [smul_eq_mul]
    rw [mul_comm (of K f a * y K f * c) (2 * y K f), hcoeffirst, hcoef]
  have hinj : Function.Injective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    intro r s h
    have hh := congrArg l h
    simpa only [LinearMap.toSpanSingleton_apply, map_smul, hl, smul_eq_mul, mul_one] using hh
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact hspan
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton A Ω[A⁄K] w) ⟨hinj, hsurj⟩).symm⟩

end MazurTransfer.IntegralHyperellipticCoordinateDifferentials

#print axioms MazurTransfer.IntegralHyperellipticCoordinateDifferentials.tangentDerivation
#print axioms MazurTransfer.IntegralHyperellipticCoordinateDifferentials.kaehler_equiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: relative dimension one from genuine Kaehler differentials
for smooth domain algebras. Named downstream consumer: the actual order-thirteen
chart morphisms. This uses genuine localization of the differential module.
-/

noncomputable section
open Module
namespace MazurTransfer
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

theorem locally_standardSmooth_relativeDimension_one_of_kaehler_equiv
    [Algebra.Smooth R S] (he : Nonempty (Ω[S⁄R] ≃ₗ[S] S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S) := by
  classical
  obtain ⟨e⟩ := he
  let b : Basis Unit S Ω[S⁄R] := (Basis.singleton Unit S).map e.symm
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  have hs' : Ideal.span {x : S | x ∈ s ∧ x ≠ 0} = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Ideal.span_le.mpr
    intro x hx
    by_cases hz : x = 0
    · subst x
      exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨hx, hz⟩
  refine ⟨_, hs', fun x hx ↦ ?_⟩
  let T := Localization.Away x
  have : IsDomain T := Localization.Away.isDomain hx.2
  have : Algebra.IsStandardSmooth R T := h x hx.1
  let bT : Basis Unit T Ω[T⁄R] := b.ofIsLocalizedModule T (Submonoid.powers x)
    (KaehlerDifferential.map R R S T)
  rw [← IsScalarTower.algebraMap_eq R S T]
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R T)
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr
  simp only [rank_eq_card_basis bT, Cardinal.mk_fintype, Fintype.card_unique,
    Nat.cast_one]

end MazurTransfer
#print axioms MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal smooth integral curve over Z[1/104].
Named downstream consumer: identifying the rational and finite-field fibres
of this actual family for compatible Picard good reduction.
This proves smoothness, flatness and local finite presentation; properness
and fibre compatibility are separate conclusions still to be constructed.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralBase
open CategoryTheory AlgebraicGeometry

abbrev BaseRing := Localization.Away (104 : ℤ)

theorem unit104 : IsUnit (104 : BaseRing) := by
  simpa only [map_ofNat] using
    (IsLocalization.Away.algebraMap_isUnit (S := BaseRing) (104 : ℤ))

end MazurTransfer.Order13IntegralBase

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual coefficient ring Z[1/104] is noetherian
and reduced. Named downstream consumer: integral Picard representability.
-/

namespace MazurTransfer.Order13IntegralBase

theorem actualBase_isNoetherianRing : IsNoetherianRing BaseRing := inferInstance

theorem actualBase_isReduced : IsReduced BaseRing := inferInstance

end MazurTransfer.Order13IntegralBase
#print axioms MazurTransfer.Order13IntegralBase.actualBase_isNoetherianRing
#print axioms MazurTransfer.Order13IntegralBase.actualBase_isReduced

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: smoothness of the actual two-chart integral curve over any
commutative ring in which 104 is a unit. Explicit integral Bezout identities
and square-zero lifting prove the assertion; no smooth model is assumed.
Named downstream consumer: compatible good reduction of the order-thirteen
curve and its Picard scheme at the primes 3 and 5.
-/

noncomputable section
universe u
open Polynomial CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

namespace MazurTransfer.Order13IntegralSmoothCurve
variable (K : Type u) [CommRing K] (h104 : IsUnit (104 : K))
include h104

theorem sexticPolynomial_isCoprime_derivative : IsCoprime (sexticPolynomial K) (sexticPolynomial K).derivative := by
  obtain ⟨u, hu⟩ := h104
  have hinv : ↑(u⁻¹) * (104 : K) = 1 := by
    rw [← hu]
    simp
  let A : Polynomial K := 300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548
  let B : Polynomial K := -50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 -
    278 * X - 111
  have hbezout : A * sexticPolynomial K + B * (sexticPolynomial K).derivative = C 104 := by
    simp only [A, B, sexticPolynomial, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_natCast, mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  refine ⟨C (↑(u⁻¹) : K) * A, C (↑(u⁻¹) : K) * B, ?_⟩
  calc
    _ = C (↑(u⁻¹) : K) * (A * sexticPolynomial K + B * (sexticPolynomial K).derivative) := by ring
    _ = C (↑(u⁻¹) : K) * C 104 := by rw [hbezout]
    _ = 1 := by rw [← map_mul, hinv, C_1]


theorem reciprocalPolynomial_isCoprime_derivative : IsCoprime (reciprocalPolynomial K) (reciprocalPolynomial K).derivative := by
  obtain ⟨u, hu⟩ := h104
  have hinv : ↑(u⁻¹) * (104 : K) = 1 := by
    rw [← hu]
    simp
  let A : Polynomial K := 300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234
  let B : Polynomial K := -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 -
    73 * X - 65
  have hbezout : A * reciprocalPolynomial K + B * (reciprocalPolynomial K).derivative = C 104 := by
    simp only [A, B, reciprocalPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_natCast,
      mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  refine ⟨C (↑(u⁻¹) : K) * A, C (↑(u⁻¹) : K) * B, ?_⟩
  calc
    _ = C (↑(u⁻¹) : K) * (A * reciprocalPolynomial K + B *
      (reciprocalPolynomial K).derivative) := by ring
    _ = 1 := by rw [hbezout, ← C_mul, hinv, C_1]


theorem two_isUnit : IsUnit (2 : K) := by
  have h : IsUnit ((2 : K) * 52) := by
    convert h104 using 1; norm_num
  exact (IsUnit.mul_iff.mp h).1

theorem ordinaryCoordinateRing_smooth : Algebra.Smooth K (CoordinateRing K) := by
  letI : Smooth (curveToBase K) :=
    (MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).2.2 h104
  have h : Smooth (ordinaryChartToBase K) := by
    rw [← ordinaryChartMap_curveToBase]
    infer_instance
  unfold ordinaryChartToBase at h
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

theorem reciprocalRing_smooth : Algebra.Smooth K (ReciprocalRing K) := by
  letI : Smooth (curveToBase K) :=
    (MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).2.2 h104
  have h : Smooth (reciprocalChartToBase K) := by
    rw [← reciprocalChartMap_curveToBase]
    infer_instance
  unfold reciprocalChartToBase at h
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

end MazurTransfer.Order13IntegralSmoothCurve

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual curve integrality and domain coordinate rings over
noetherian integral bases where 104 is a unit. Named downstream consumer:
relative dimension one from the constructed Kaehler differential modules.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralCurveDomains
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (K : Type u) [CommRing K] [IsDomain K] [IsNoetherianRing K]
    (h104 : IsUnit (104 : K))
include h104

theorem curveScheme_isIntegral : IsIntegral (curveScheme K) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_integral_curve_geometrically_integral K h104
  letI : Flat (curveToBase K) := (MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).1
  letI : Smooth (curveToBase K) := (MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).2.2 h104
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (curveToBase K)

theorem coordinateRing_isDomain : IsDomain (CoordinateRing K) := by
  letI : Nontrivial (CoordinateRing K) := Function.Injective.nontrivial
    (QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).symm.injective
  letI : IsIntegral (curveScheme K) := curveScheme_isIntegral K h104
  have : IsIntegral (MazurTorsion.XOneThirteenAffineCurve.scheme K) :=
    isIntegral_of_isOpenImmersion (ordinaryChartMap K)
  exact (affine_isIntegral_iff (.of (CoordinateRing K))).mp this

theorem reciprocalRing_isDomain : IsDomain (ReciprocalRing K) := by
  letI : Nontrivial (ReciprocalRing K) := Function.Injective.nontrivial
    (QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm.injective
  letI : IsIntegral (curveScheme K) := curveScheme_isIntegral K h104
  have : IsIntegral (reciprocalScheme K) :=
    isIntegral_of_isOpenImmersion (reciprocalChartMap K)
  exact (affine_isIntegral_iff (.of (ReciprocalRing K))).mp this

end MazurTransfer.Order13IntegralCurveDomains
#print axioms MazurTransfer.Order13IntegralCurveDomains.curveScheme_isIntegral
#print axioms MazurTransfer.Order13IntegralCurveDomains.coordinateRing_isDomain
#print axioms MazurTransfer.Order13IntegralCurveDomains.reciprocalRing_isDomain

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: smoothness of relative dimension exactly one for the
actual order-13 curve over noetherian integral bases where 104 is a unit.
Named downstream consumer: the actual integral Picard representability
contract over Z[1/104]. No relative-dimension or differential-rank input
is assumed: the full differential equivalences are constructed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralRelativeDimension
open Polynomial CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (K : Type u) [CommRing K] [IsDomain K] [IsNoetherianRing K]
    (h104 : IsUnit (104 : K))
include h104

theorem ordinaryCoordinateRing_kaehler_equiv :
    Nonempty (Ω[CoordinateRing K⁄K] ≃ₗ[CoordinateRing K] CoordinateRing K) :=
  IntegralHyperellipticCoordinateDifferentials.kaehler_equiv K (sexticPolynomial K)
    (Order13IntegralSmoothCurve.sexticPolynomial_isCoprime_derivative K h104)
    (Order13IntegralSmoothCurve.two_isUnit K h104)

theorem reciprocalRing_kaehler_equiv :
    Nonempty (Ω[ReciprocalRing K⁄K] ≃ₗ[ReciprocalRing K] ReciprocalRing K) :=
  IntegralHyperellipticCoordinateDifferentials.kaehler_equiv K (reciprocalPolynomial K)
    (Order13IntegralSmoothCurve.reciprocalPolynomial_isCoprime_derivative K h104)
    (Order13IntegralSmoothCurve.two_isUnit K h104)

theorem ordinaryChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (ordinaryChartToBase K) := by
  letI : IsDomain (CoordinateRing K) :=
    Order13IntegralCurveDomains.coordinateRing_isDomain K h104
  letI : Algebra.Smooth K (CoordinateRing K) :=
    Order13IntegralSmoothCurve.ordinaryCoordinateRing_smooth K h104
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (CoordinateRing K) (ordinaryCoordinateRing_kaehler_equiv K h104)

theorem reciprocalChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (reciprocalChartToBase K) := by
  letI : IsDomain (ReciprocalRing K) :=
    Order13IntegralCurveDomains.reciprocalRing_isDomain K h104
  letI : Algebra.Smooth K (ReciprocalRing K) :=
    Order13IntegralSmoothCurve.reciprocalRing_smooth K h104
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (ReciprocalRing K) (reciprocalRing_kaehler_equiv K h104)

theorem curveToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (curveToBase K) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change SmoothOfRelativeDimension 1 (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth_relativeDimension_one K h104
  · change SmoothOfRelativeDimension 1 (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth_relativeDimension_one K h104

end MazurTransfer.Order13IntegralRelativeDimension

namespace MazurTransfer.Order13IntegralBase
open AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem actual_curveToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (curveToBase BaseRing) := by
  letI : IsDomain BaseRing := Localization.Away.isDomain (by norm_num : (104 : ℤ) ≠ 0)
  letI : IsNoetherianRing BaseRing := actualBase_isNoetherianRing
  exact Order13IntegralRelativeDimension.curveToBase_smooth_relativeDimension_one
    BaseRing unit104

end MazurTransfer.Order13IntegralBase
#print axioms MazurTransfer.Order13IntegralRelativeDimension.ordinaryCoordinateRing_kaehler_equiv
#print axioms MazurTransfer.Order13IntegralRelativeDimension.reciprocalRing_kaehler_equiv
#print axioms MazurTransfer.Order13IntegralRelativeDimension.curveToBase_smooth_relativeDimension_one
#print axioms MazurTransfer.Order13IntegralBase.actual_curveToBase_smooth_relativeDimension_one

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: relative dimension exactly one over every commutative
ring where 104 is invertible, by scalar extension from the actual
noetherian integral base. Named downstream consumer: integral Picard
representability and base-change-compatible rational and finite fibres.
The universe lift is a ring equivalence, not a new mathematical base.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralRelativeDimension
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralBase

theorem curveToBase_smooth_relativeDimension_one_over_every_ring
    (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    SmoothOfRelativeDimension 1 (curveToBase R) := by
  letI : IsDomain BaseRing := Localization.Away.isDomain (by norm_num : (104 : ℤ) ≠ 0)
  letI : IsNoetherianRing BaseRing := actualBase_isNoetherianRing
  let K := ULift.{u} BaseRing
  letI : IsDomain K := (ULift.ringEquiv : K ≃+* BaseRing).toMulEquiv.isDomain BaseRing
  letI : IsNoetherianRing K :=
    isNoetherianRing_of_ringEquiv BaseRing (ULift.ringEquiv.symm : BaseRing ≃+* K)
  have hK : IsUnit (104 : K) := by
    simpa only [map_ofNat] using unit104.map
      (ULift.ringEquiv.symm.toRingHom : BaseRing →+* K)
  let g : BaseRing →+* R := IsLocalization.Away.lift (104 : ℤ)
    (g := Int.castRingHom R) (by simpa only [map_ofNat] using h104)
  let f : K →+* R := g.comp ULift.ringEquiv.toRingHom
  letI : Algebra K R := f.toAlgebra
  letI : SmoothOfRelativeDimension 1 (curveToBase K) :=
    curveToBase_smooth_relativeDimension_one K hK
  let P : MorphismProperty Scheme.{u} := @SmoothOfRelativeDimension 1
  letI : P.IsStableUnderBaseChange :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  obtain ⟨e, φA, φB, he, hrest⟩ :=
    MazurTransfer.order13_actual_whole_curve_base_change_isomorphism K R
  letI : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R))) (curveToBase K)) :=
    MorphismProperty.pullback_fst (P := P) _ _ inferInstance
  have h : SmoothOfRelativeDimension 1 (e.inv ≫ pullback.fst _ _) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.inv ≫ pullback.fst _ _))
  rw [he] at h
  exact h

end MazurTransfer.Order13IntegralRelativeDimension
#print axioms MazurTransfer.Order13IntegralRelativeDimension.curveToBase_smooth_relativeDimension_one_over_every_ring

end
end

end IntegralRelativeDimensionPublicProof

theorem solution.{u}
    (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    SmoothOfRelativeDimension 1 (curveToBase R) := by
  exact IntegralRelativeDimensionPublicProof.MazurTransfer.Order13IntegralRelativeDimension.curveToBase_smooth_relativeDimension_one_over_every_ring R h104

#print axioms solution
