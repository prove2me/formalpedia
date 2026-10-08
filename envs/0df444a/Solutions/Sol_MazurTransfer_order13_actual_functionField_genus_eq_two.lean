-- Prove2me | solution 1 for MazurTransfer.order13_actual_functionField_genus_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-08T01:00:16.92836+00:00
-- url     : https://prove2.me/submissions/45b5087e-5f52-4f16-87fa-c9b5f3c63d91

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
open AlgebraicGeometry CategoryTheory

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
No genus or Jacobian assertion is assumed.
-/

noncomputable section
namespace MazurTransfer.HyperellipticCoordinateDifferentials
open Polynomial Module
variable (K : Type*) [Field K] (f : Polynomial K)

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

theorem kaehler_equiv (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Nonempty (Ω[CoordinateRing K f⁄K] ≃ₗ[CoordinateRing K f] CoordinateRing K f) := by
  rw [separable_def'] at hf
  obtain ⟨a, b, hab⟩ := hf
  let A := CoordinateRing K f
  let d := KaehlerDifferential.D K A
  let c : A := algebraMap K A ((2 : K)⁻¹)
  have hc : (2 : A) * c = 1 := by
    calc
      _ = algebraMap K A ((2 : K) * (2 : K)⁻¹) := by simp only [c, map_mul, map_ofNat]
      _ = 1 := by rw [mul_inv_cancel₀ h2, map_one]
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

end MazurTransfer.HyperellipticCoordinateDifferentials

#print axioms MazurTransfer.HyperellipticCoordinateDifferentials.tangentDerivation
#print axioms MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv

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
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine smoothness of a quadratic hyperelliptic coordinate
algebra over a field of characteristic different from two. Named downstream consumer: smoothness of
MazurTorsion.XOneThirteenAffineCurve.scheme and the two-chart curve.
The polynomial separability hypothesis is explicit and separately checked
for the actual order-thirteen sextic.
-/

noncomputable section
open Polynomial

namespace MazurTransfer

universe u
variable (K : Type u) [Field K]

theorem hyperelliptic_coordinate_smooth (f : Polynomial K) (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (AdjoinRoot
      ((X ^ 2 - C f) : Polynomial (Polynomial K))) := by
  let q : Polynomial (Polynomial K) := X ^ 2 - C f
  have hroot : AdjoinRoot.root q ^ 2 = AdjoinRoot.of q f := by
    apply sub_eq_zero.mp
    simpa only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using
      AdjoinRoot.eval₂_root q
  rw [separable_def'] at hf
  obtain ⟨a, b, hab⟩ := hf
  haveI : Algebra.FormallySmooth K (AdjoinRoot q) := by
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI φ
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.of q X))
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.root q))
    have hφpoly : φ.comp (AdjoinRoot.ofAlgHom K q) =
        aeval (φ (AdjoinRoot.of q X)) := by
      apply Polynomial.algHom_ext
      simp
    have hφrelation : φ (AdjoinRoot.root q) ^ 2 =
        aeval (φ (AdjoinRoot.of q X)) f := by
      calc
        _ = φ (AdjoinRoot.of q f) := by
          simpa only [_root_.map_pow] using congrArg φ hroot
        _ = _ := DFunLike.congr_fun hφpoly f
    let e : B := y ^ 2 - aeval x f
    have hmap : (Ideal.Quotient.mkₐ K I).comp (aeval x) =
        aeval (Ideal.Quotient.mk I x) := by
      apply Polynomial.algHom_ext
      simp
    have hmapf : Ideal.Quotient.mkₐ K I (aeval x f) =
        aeval (Ideal.Quotient.mk I x) f := DFunLike.congr_fun hmap f
    have he0 : Ideal.Quotient.mkₐ K I e = 0 := by
      change Ideal.Quotient.mkₐ K I (y ^ 2 - aeval x f) = 0
      rw [_root_.map_sub, _root_.map_pow, hmapf]
      change Ideal.Quotient.mk I y ^ 2 - aeval (Ideal.Quotient.mk I x) f = 0
      rw [hx, hy, hφrelation, sub_self]
    have heI : e ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      exact he0
    have sqzero {z : B} (hz : z ∈ I) : z ^ 2 = 0 := by
      have hz2 := Ideal.mul_mem_mul hz hz
      rw [← pow_two, hI] at hz2
      simpa only [Ideal.mem_bot, pow_two] using hz2
    have he2 : e ^ 2 = 0 := sqzero heI
    let av : B := aeval x a
    let bv : B := aeval x b
    let c : B := algebraMap K B ((2 : K)⁻¹)
    have hc : (2 : B) * c = 1 := by
      calc
        _ = algebraMap K B ((2 : K) * (2 : K)⁻¹) := by
          simp only [c, _root_.map_mul, _root_.map_ofNat]
        _ = 1 := by rw [mul_inv_cancel₀ h2, _root_.map_one]
    let dx : B := e * bv
    let dy : B := -(e * av * y * c)
    have hdxI : dx ∈ I := I.mul_mem_right bv heI
    have hdyI : dy ∈ I := I.neg_mem
      (I.mul_mem_right c (I.mul_mem_right y (I.mul_mem_right av heI)))
    have hdx2 : dx ^ 2 = 0 := sqzero hdxI
    have hdy2 : dy ^ 2 = 0 := sqzero hdyI
    have hjac : av * aeval x f + bv * aeval x f.derivative = 1 := by
      simpa only [av, bv, _root_.map_add, _root_.map_mul, _root_.map_one] using
        congrArg (aeval x) hab
    have hjac' : av * y ^ 2 + bv * aeval x f.derivative = 1 + av * e := by
      calc
        _ = (av * aeval x f + bv * aeval x f.derivative) + av * e := by
          dsimp [e]
          ring
        _ = _ := by rw [hjac]
    have hdyterm : 2 * y * dy = -(e * av * y ^ 2) := by
      calc
        _ = -(e * av * y ^ 2 * (2 * c)) := by dsimp [dy]; ring
        _ = _ := by rw [hc]; ring
    have hlift : (y + dy) ^ 2 = aeval (x + dx) f := by
      rw [aeval_add_of_sq_eq_zero f x dx hdx2]
      apply sub_eq_zero.mp
      calc
        _ = (y ^ 2 - aeval x f) + 2 * y * dy + dy ^ 2 -
            aeval x f.derivative * dx := by ring
        _ = e - e * (av * y ^ 2 + bv * aeval x f.derivative) := by
          rw [hdyterm, hdy2]
          dsimp [e, dx]
          ring
        _ = 0 := by rw [hjac']; ring_nf; rw [he2]; ring
    let ψ : AdjoinRoot q →ₐ[K] B :=
      AdjoinRoot.liftAlgHom q (aeval (x + dx)) (y + dy) (by
        simp only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        exact sub_eq_zero.mpr hlift)
    refine ⟨ψ, ?_⟩
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom,
        ψ, AdjoinRoot.liftAlgHom_of, aeval_X]
      change Ideal.Quotient.mk I (x + dx) = φ (AdjoinRoot.of q X)
      simp only [_root_.map_add, dx, _root_.map_mul]
      change Ideal.Quotient.mk I x + Ideal.Quotient.mkₐ K I e *
        Ideal.Quotient.mk I bv = _
      rw [he0, zero_mul, add_zero, hx]
    · simp only [AlgHom.comp_apply, ψ, AdjoinRoot.liftAlgHom_root]
      change Ideal.Quotient.mk I (y + dy) = φ (AdjoinRoot.root q)
      simp only [_root_.map_add, dy, _root_.map_neg, _root_.map_mul]
      change Ideal.Quotient.mk I y + -(Ideal.Quotient.mkₐ K I e *
        Ideal.Quotient.mk I av * Ideal.Quotient.mk I y * Ideal.Quotient.mk I c) = _
      rw [he0, zero_mul, zero_mul, zero_mul, neg_zero, add_zero, hy]
  exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

end MazurTransfer

#print axioms MazurTransfer.hyperelliptic_coordinate_smooth

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual quadratic coordinate algebra of the order-13
affine chart. The named downstream consumer `coordinateRing_isDomain` uses
the irreducibility certificate below. No smoothness, genus, or Jacobian
assertion is assumed in this interface.
-/

noncomputable section

open Polynomial

namespace MazurTorsion.XOneThirteenAffineCurve

variable (K : Type*) [Field K] [CharZero K]

theorem sexticPolynomial_separable : (sexticPolynomial K).Separable := by
  let A : Polynomial K := 300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548
  let B : Polynomial K := -50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 -
    278 * X - 111
  have hbezout : A * sexticPolynomial K + B * (sexticPolynomial K).derivative = C 104 := by
    simp only [A, B, sexticPolynomial, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_natCast, mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  rw [separable_def']
  refine ⟨C ((104 : K)⁻¹) * A, C ((104 : K)⁻¹) * B, ?_⟩
  calc
    _ = C ((104 : K)⁻¹) * (A * sexticPolynomial K + B * (sexticPolynomial K).derivative) := by ring
    _ = C ((104 : K)⁻¹) * C 104 := by rw [hbezout]
    _ = 1 := by rw [← map_mul]; norm_num

theorem sexticPolynomial_not_square (q : Polynomial K) : q ^ 2 ≠ sexticPolynomial K := by
  intro hq
  have hunit : IsUnit q := (sexticPolynomial_separable K).squarefree q (by
    rw [← hq, pow_two])
  have hdegree : (sexticPolynomial K).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit (hq ▸ hunit.pow 2)
  have hdegree6 : (sexticPolynomial K).natDegree = 6 := by
    unfold sexticPolynomial
    compute_degree!
  omega

theorem sexticPolynomial_fraction_not_square (q : RatFunc K) :
    q ^ 2 ≠ algebraMap (Polynomial K) (RatFunc K) (sexticPolynomial K) := by
  intro hq
  have hIntegral : IsIntegral (Polynomial K) (q ^ 2) := by
    rw [hq]
    exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Polynomial K) (K := RatFunc K) (by decide : 0 < 2) hIntegral
  apply sexticPolynomial_not_square K r
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  rw [map_pow, hr, hq]

theorem affineEquation_irreducible : Irreducible (affineEquation K) := by
  have hmonic : (affineEquation K).Monic := by
    unfold affineEquation
    exact monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mpr
  simp only [affineEquation, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 2)
    (sexticPolynomial_fraction_not_square K)

theorem coordinateRing_isDomain : IsDomain (CoordinateRing K) :=
  AdjoinRoot.isDomain_of_prime (affineEquation_irreducible K).prime

theorem affineScheme_isIntegral : _root_.AlgebraicGeometry.IsIntegral (scheme K) := by
  letI := coordinateRing_isDomain K
  exact inferInstance

end MazurTorsion.XOneThirteenAffineCurve

#print axioms MazurTorsion.XOneThirteenAffineCurve.coordinateRing_isDomain

#print axioms MazurTorsion.XOneThirteenAffineCurve.affineScheme_isIntegral

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual reciprocal coordinate algebra and the reduced
two-chart gluing. The downstream consumers `reciprocalScheme_isIntegral`
and `curveScheme_isReduced` use the coordinate-domain certificates.
No Jacobian, genus, or rank-zero assertion is assumed.
-/

noncomputable section

open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.XOneThirteenProjectiveCurve

theorem reciprocalPolynomial_affineSwap (K : Type*) [CommRing K] :
    aeval (-(X : Polynomial K) - 1) (reciprocalPolynomial K) =
      XOneThirteenAffineCurve.sexticPolynomial K := by
  simp only [reciprocalPolynomial, _root_.map_add, _root_.map_mul,
    _root_.map_pow, _root_.map_ofNat, aeval_X, _root_.map_one]
  unfold XOneThirteenAffineCurve.sexticPolynomial
  ring

variable (K : Type*) [Field K] [CharZero K]

theorem reciprocalPolynomial_not_square (q : Polynomial K) :
    q ^ 2 ≠ reciprocalPolynomial K := by
  intro hq
  have h := congrArg (aeval (-(X : Polynomial K) - 1)) hq
  rw [_root_.map_pow, reciprocalPolynomial_affineSwap] at h
  exact XOneThirteenAffineCurve.sexticPolynomial_not_square K _ h

theorem reciprocalPolynomial_fraction_not_square (q : RatFunc K) :
    q ^ 2 ≠ algebraMap (Polynomial K) (RatFunc K) (reciprocalPolynomial K) := by
  intro hq
  have hIntegral : IsIntegral (Polynomial K) (q ^ 2) := by
    rw [hq]
    exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Polynomial K) (K := RatFunc K) (by decide : 0 < 2) hIntegral
  apply reciprocalPolynomial_not_square K r
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  rw [_root_.map_pow, hr, hq]

theorem reciprocalEquation_irreducible : Irreducible (reciprocalEquation K) := by
  have hmonic : (reciprocalEquation K).Monic := by
    unfold reciprocalEquation
    exact monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mpr
  simp only [reciprocalEquation, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 2)
    (reciprocalPolynomial_fraction_not_square K)

theorem reciprocalRing_isDomain : IsDomain (ReciprocalRing K) :=
  AdjoinRoot.isDomain_of_prime (reciprocalEquation_irreducible K).prime

theorem reciprocalScheme_isIntegral : _root_.AlgebraicGeometry.IsIntegral (reciprocalScheme K) := by
  letI := reciprocalRing_isDomain K
  exact inferInstance

theorem curveScheme_isReduced : _root_.AlgebraicGeometry.IsReduced (curveScheme K) := by
  letI := XOneThirteenAffineCurve.affineScheme_isIntegral K
  letI := reciprocalScheme_isIntegral K
  letI : ∀ i : (glueData K).openCover.I₀,
      _root_.AlgebraicGeometry.IsReduced ((glueData K).openCover.X i) := by
    intro i
    cases i
    · change _root_.AlgebraicGeometry.IsReduced (XOneThirteenAffineCurve.scheme K)
      infer_instance
    · change _root_.AlgebraicGeometry.IsReduced (reciprocalScheme K)
      infer_instance
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover (curveScheme K) (glueData K).openCover

end MazurTorsion.XOneThirteenProjectiveCurve

#print axioms MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme_isIntegral
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isReduced

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine scheme smoothness of the unchanged order-thirteen
model over a characteristic-zero field. Named downstream consumer:
`curveToBase_smooth`, for the subsequent curve/Picard interface.
-/

noncomputable section
open Polynomial _root_.AlgebraicGeometry CategoryTheory

namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem ordinaryCoordinateRing_smooth : Algebra.Smooth K
    (XOneThirteenAffineCurve.CoordinateRing K) :=
  MazurTransfer.hyperelliptic_coordinate_smooth K
    (XOneThirteenAffineCurve.sexticPolynomial K)
    (XOneThirteenAffineCurve.sexticPolynomial_separable K) (by norm_num)

theorem reciprocalPolynomial_separable : (reciprocalPolynomial K).Separable := by
  let A : Polynomial K := 300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234
  let B : Polynomial K := -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 -
    73 * X - 65
  have hbezout : A * reciprocalPolynomial K + B * (reciprocalPolynomial K).derivative = C 104 := by
    simp only [A, B, reciprocalPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_natCast,
      mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  rw [separable_def']
  refine ⟨C ((104 : K)⁻¹) * A, C ((104 : K)⁻¹) * B, ?_⟩
  calc
    _ = C ((104 : K)⁻¹) * (A * reciprocalPolynomial K + B *
      (reciprocalPolynomial K).derivative) := by ring
    _ = 1 := by rw [hbezout, ← C_mul]; norm_num

theorem reciprocalRing_smooth : Algebra.Smooth K (ReciprocalRing K) :=
  MazurTransfer.hyperelliptic_coordinate_smooth K (reciprocalPolynomial K)
    (reciprocalPolynomial_separable K) (by norm_num)

theorem ordinaryChartToBase_smooth : Smooth (ordinaryChartToBase K) := by
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (ordinaryCoordinateRing_smooth K)

theorem reciprocalChartToBase_smooth : Smooth (reciprocalChartToBase K) := by
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (reciprocalRing_smooth K)

theorem curveToBase_smooth : Smooth (curveToBase K) := by
  haveI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Smooth.{u}) (Q := @RingHom.Smooth.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u})
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change Smooth (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth K
  · change Smooth (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth K

end MazurTorsion.XOneThirteenProjectiveCurve

#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual relative-dimension-one smoothness of the unchanged
order-thirteen glued curve. Named downstream consumer: the official FLT
smooth-proper-curve scheme-to-genus comparison. No genus assertion is assumed.
-/

noncomputable section
open Polynomial _root_.AlgebraicGeometry CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem ordinaryCoordinateRing_kaehler_equiv :
    Nonempty (Ω[XOneThirteenAffineCurve.CoordinateRing K⁄K] ≃ₗ[
      XOneThirteenAffineCurve.CoordinateRing K] XOneThirteenAffineCurve.CoordinateRing K) :=
  MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv K
    (XOneThirteenAffineCurve.sexticPolynomial K)
    (XOneThirteenAffineCurve.sexticPolynomial_separable K) (by norm_num)

theorem reciprocalRing_kaehler_equiv :
    Nonempty (Ω[ReciprocalRing K⁄K] ≃ₗ[ReciprocalRing K] ReciprocalRing K) :=
  MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv K
    (reciprocalPolynomial K) (reciprocalPolynomial_separable K) (by norm_num)

theorem ordinaryChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (ordinaryChartToBase K) := by
  have : IsDomain (XOneThirteenAffineCurve.CoordinateRing K) :=
    XOneThirteenAffineCurve.coordinateRing_isDomain K
  have : Algebra.Smooth K (XOneThirteenAffineCurve.CoordinateRing K) :=
    ordinaryCoordinateRing_smooth K
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (XOneThirteenAffineCurve.CoordinateRing K) (ordinaryCoordinateRing_kaehler_equiv K)

theorem reciprocalChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (reciprocalChartToBase K) := by
  have : IsDomain (ReciprocalRing K) := reciprocalRing_isDomain K
  have : Algebra.Smooth K (ReciprocalRing K) := reciprocalRing_smooth K
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (ReciprocalRing K) (reciprocalRing_kaehler_equiv K)

theorem curveToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (curveToBase K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{u} 1)
      (Q := @RingHom.Locally.{u}
        (@RingHom.IsStandardSmoothOfRelativeDimension.{u,u} 1))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} 1)
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change SmoothOfRelativeDimension 1 (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth_relativeDimension_one K
  · change SmoothOfRelativeDimension 1 (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth_relativeDimension_one K

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.ordinaryCoordinateRing_kaehler_equiv
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.reciprocalRing_kaehler_equiv
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth_relativeDimension_one

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: integral two-chart gluing, with explicit chart-integrality
and nonempty-overlap assumptions. Named downstream consumer:
MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isIntegral; its hypotheses
are independently checked on the original order-thirteen model.
-/

noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace MazurTransfer

theorem irreducible_of_two_open_charts
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A → C) (g : B → C) (hf : Continuous f) (hg : Continuous g)
    (hfo : IsOpen (Set.range f))
    (hcover : ∀ c, c ∈ Set.range f ∨ c ∈ Set.range g)
    (hoverlap : ∃ a b, f a = g b) : IrreducibleSpace C := by
  obtain ⟨a, b, hab⟩ := hoverlap
  have hpre (U : Set C) (hU : IsOpen U) (hne : U.Nonempty) :
      (f ⁻¹' U).Nonempty := by
    obtain ⟨c, hc⟩ := hne
    rcases hcover c with ⟨a', rfl⟩ | ⟨b', rfl⟩
    · exact ⟨a', hc⟩
    · obtain ⟨z, hzU, hzF⟩ := nonempty_preirreducible_inter
        (hU.preimage hg) (hfo.preimage hg) ⟨b', hc⟩ ⟨b, a, hab⟩
      obtain ⟨a', ha'⟩ := hzF
      refine ⟨a', ?_⟩
      change f a' ∈ U
      rw [ha']
      exact hzU
  haveI : PreirreducibleSpace C := PreirreducibleSpace.of_forall_nonempty_inter
    (by
      intro U V hU hV hUn hVn
      obtain ⟨a', haU, haV⟩ := nonempty_preirreducible_inter
        (hU.preimage hf) (hV.preimage hf) (hpre U hU hUn) (hpre V hV hVn)
      exact ⟨f a', haU, haV⟩)
  exact { toNonempty := Nonempty.map f inferInstance }


theorem integral_of_two_chart_gluing
    (D : Scheme.GlueData) (i j : D.J) (hcover : ∀ k, k = i ∨ k = j)
    [IsIntegral (D.U i)] [IsIntegral (D.U j)]
    (hoverlap : Nonempty (D.V (i, j))) : IsIntegral D.glued := by
  have hr : ∀ k : D.openCover.I₀, IsReduced (D.openCover.X k) := by
    intro k
    change IsReduced (D.U k)
    rcases hcover k with h | h
    · rw [h]; infer_instance
    · rw [h]; infer_instance
  haveI := hr
  haveI : IsReduced D.glued := IsReduced.of_openCover D.glued D.openCover
  have hpoint : ∃ a b, D.ι i a = D.ι j b := by
    let z := Classical.choice hoverlap
    exact ⟨D.f i j z, (D.t i j ≫ D.f j i) z,
      (D.ι_eq_iff i j _ _).mpr ⟨z, rfl, rfl⟩⟩
  haveI : IrreducibleSpace D.glued := irreducible_of_two_open_charts
    (D.ι i) (D.ι j) (D.ι i).continuous (D.ι j).continuous
    (D.ι i).isOpenEmbedding.isOpen_range (by
      intro c
      obtain ⟨k, x, hx⟩ := D.ι_jointly_surjective c
      rcases hcover k with rfl | rfl
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩) hpoint
  exact isIntegral_of_irreducibleSpace_of_isReduced D.glued

end MazurTransfer

theorem order13_two_chart_integrality_solution (D : _root_.AlgebraicGeometry.Scheme.GlueData)
    (i j : D.J) (hcover : ∀ k, k = i ∨ k = j)
    [_root_.AlgebraicGeometry.IsIntegral (D.U i)]
    [_root_.AlgebraicGeometry.IsIntegral (D.U j)]
    (hoverlap : Nonempty (D.V (i, j))) :
    _root_.AlgebraicGeometry.IsIntegral D.glued :=
  MazurTransfer.integral_of_two_chart_gluing D i j hcover hoverlap

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: integrality of the unchanged two-chart order-thirteen model.
The downstream consumer is `curveScheme_isIntegral`. This proof supplies no
smoothness, genus, Picard identification, or rational-point classification.
-/

noncomputable section

open _root_.AlgebraicGeometry CategoryTheory

namespace MazurTorsion.XOneThirteenProjectiveCurve

private theorem irreducible_of_two_open_charts_genus_import_recovery_unit9
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A → C) (g : B → C) (hf : Continuous f) (hg : Continuous g)
    (hfo : IsOpen (Set.range f))
    (hcover : ∀ c, c ∈ Set.range f ∨ c ∈ Set.range g)
    (hoverlap : ∃ a b, f a = g b) : IrreducibleSpace C := by
  obtain ⟨a, b, hab⟩ := hoverlap
  have hpre (U : Set C) (hU : IsOpen U) (hne : U.Nonempty) :
      (f ⁻¹' U).Nonempty := by
    obtain ⟨c, hc⟩ := hne
    rcases hcover c with ⟨a', rfl⟩ | ⟨b', rfl⟩
    · exact ⟨a', hc⟩
    · obtain ⟨z, hzU, hzF⟩ := nonempty_preirreducible_inter
        (hU.preimage hg) (hfo.preimage hg) ⟨b', hc⟩ ⟨b, a, hab⟩
      obtain ⟨a', ha'⟩ := hzF
      refine ⟨a', ?_⟩
      change f a' ∈ U
      rw [ha']
      exact hzU
  haveI : PreirreducibleSpace C := PreirreducibleSpace.of_forall_nonempty_inter
    (by
      intro U V hU hV hUn hVn
      obtain ⟨a', haU, haV⟩ := nonempty_preirreducible_inter
        (hU.preimage hf) (hV.preimage hf) (hpre U hU hUn) (hpre V hV hVn)
      exact ⟨f a', haU, haV⟩)
  exact { toNonempty := Nonempty.map f inferInstance }

universe u
variable (K : Type u) [Field K] [CharZero K]

private def cuspSolution_genus_import_recovery_unit9 : XOneThirteenAffineCurve.Solution K K :=
  ⟨((-1 : K), 1), by
    simp [XOneThirteenAffineCurve.sexticPolynomial]
    ring⟩

private noncomputable def cuspEvaluation_genus_import_recovery_unit9 :
    XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K :=
  XOneThirteenAffineCurve.solutionToAlgHom K (cuspSolution_genus_import_recovery_unit9 K)

private theorem ordinaryOverlap_nontrivial_genus_import_recovery_unit9 : Nontrivial (OrdinaryOverlapRing K) := by
  have hu : IsUnit (cuspEvaluation_genus_import_recovery_unit9 K (XOneThirteenAffineCurve.xCoordinate K)) := by
    change IsUnit (XOneThirteenAffineCurve.solutionToAlgHom K (cuspSolution_genus_import_recovery_unit9 K)
      (XOneThirteenAffineCurve.xCoordinate K))
    rw [XOneThirteenAffineCurve.solutionToAlgHom_x]
    simp [cuspSolution_genus_import_recovery_unit9]
  let e : OrdinaryOverlapRing K →ₐ[K] K := IsLocalization.Away.liftAlgHom
    (XOneThirteenAffineCurve.xCoordinate K) (f := cuspEvaluation_genus_import_recovery_unit9 K) hu
  exact e.toRingHom.domain_nontrivial

theorem chart_images_overlap :
    ∃ a b, ordinaryChartMap K a = reciprocalChartMap K b := by
  classical
  haveI := ordinaryOverlap_nontrivial_genus_import_recovery_unit9 K
  have hne : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by decide
  have hv : (glueData K).V (Chart.ordinary, Chart.reciprocal) =
      Spec (CommRingCat.of (OrdinaryOverlapRing K)) := by
    simp only [glueData, CategoryTheory.GlueData.ofGlueData', categoricalGlueData,
      dif_neg hne]
  haveI : Nonempty ((glueData K).V (Chart.ordinary, Chart.reciprocal)) := by
    rw [hv]
    infer_instance
  let z := Classical.choice (inferInstance :
    Nonempty ((glueData K).V (Chart.ordinary, Chart.reciprocal)))
  refine ⟨(glueData K).f Chart.ordinary Chart.reciprocal z,
    ((glueData K).t Chart.ordinary Chart.reciprocal ≫
      (glueData K).f Chart.reciprocal Chart.ordinary) z, ?_⟩
  exact ((glueData K).ι_eq_iff Chart.ordinary Chart.reciprocal _ _).mpr ⟨z, rfl, rfl⟩

theorem curveScheme_irreducibleSpace : IrreducibleSpace (curveScheme K) := by
  haveI := XOneThirteenAffineCurve.affineScheme_isIntegral K
  haveI := reciprocalScheme_isIntegral K
  apply irreducible_of_two_open_charts_genus_import_recovery_unit9
    (ordinaryChartMap K) (reciprocalChartMap K)
    (ordinaryChartMap K).continuous (reciprocalChartMap K).continuous
    (ordinaryChartMap K).isOpenEmbedding.isOpen_range
  · intro c
    obtain ⟨i, x, hx⟩ := (glueData K).ι_jointly_surjective c
    cases i
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  · exact chart_images_overlap K

theorem curveScheme_isIntegral : _root_.AlgebraicGeometry.IsIntegral (curveScheme K) := by
  haveI := XOneThirteenAffineCurve.affineScheme_isIntegral K
  haveI := reciprocalScheme_isIntegral K
  haveI : IsIntegral ((glueData K).U Chart.ordinary) := by
    change IsIntegral (XOneThirteenAffineCurve.scheme K)
    exact XOneThirteenAffineCurve.affineScheme_isIntegral K
  haveI : IsIntegral ((glueData K).U Chart.reciprocal) := by
    change IsIntegral (reciprocalScheme K)
    exact reciprocalScheme_isIntegral K
  apply MazurTransfer.integral_of_two_chart_gluing (glueData K)
    Chart.ordinary Chart.reciprocal
  · intro k
    cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · obtain ⟨a, b, hab⟩ := chart_images_overlap K
    obtain ⟨z, _, _⟩ := ((glueData K).ι_eq_iff Chart.ordinary Chart.reciprocal a b).mp hab
    exact ⟨z⟩

end MazurTorsion.XOneThirteenProjectiveCurve

#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isIntegral

end

end


section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# The projective line and its generic points

This file realizes the projective line over a field `K` as the projective spectrum of the
standard grading on `K[X₀, X₁]`. A field extension map `K → F` and an element `g : F` determine
the `F`-valued point `[g : 1]`.

For an integral curve with function field `F`, this is the generic-point morphism attached to a
rational function. It is the first geometric input to the product formula in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/


open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace ProjectiveLine

noncomputable section

/-- The standard grading of the homogeneous coordinate ring `K[X₀, X₁]`. -/
abbrev homogeneousPieces (K : Type u) [Field K] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The standard graded-algebra structure on the homogeneous coordinate ring of the projective
line. Mathlib intentionally does not install this instance globally because multivariate
polynomials admit other weighted gradings. -/
noncomputable instance (K : Type u) [Field K] : GradedAlgebra (homogeneousPieces K) :=
  MvPolynomial.gradedAlgebra

/-- The projective line over `K`, realized as `Proj K[X₀, X₁]`. -/
abbrev scheme (K : Type u) [Field K] : Scheme.{u} :=
  Proj (homogeneousPieces K)

/-- The standard affine chart `D₊(X₁)` of the projective line. -/
abbrev standardAffineOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))

/-- The affine chart `D₊(X₀)` containing the point at infinity. -/
abbrev infinityAffineOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))

lemma X_one_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

lemma X_zero_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private lemma zero_lt_one_genus_import_recovery_unit10 : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- The degree-zero homogeneous fraction `X₀ / X₁` on the standard affine chart. -/
@[expose] noncomputable def affineCoordinateAway (K : Type u) [Field K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

/-- The regular function `X₀ / X₁` on the standard affine chart `D₊(X₁)`. -/
@[expose] noncomputable def affineCoordinate (K : Type u) [Field K] :
  Γ(scheme K, standardAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).hom (affineCoordinateAway K)

/-- The degree-zero homogeneous fraction `X₁ / X₀` on the affine chart containing
infinity. -/
@[expose] noncomputable def inverseAffineCoordinateAway (K : Type u) [Field K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

/-- The regular function `X₁ / X₀` on the affine chart `D₊(X₀)`. -/
@[expose] noncomputable def inverseAffineCoordinate (K : Type u) [Field K] :
    Γ(scheme K, infinityAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).hom (inverseAffineCoordinateAway K)

/-- The constant-polynomial equivalence from `K` to the degree-zero part of `K[X₀, X₁]`. -/
@[expose]
noncomputable def degreeZeroRingEquiv (K : Type u) [Field K] :
    K ≃+* homogeneousPieces K 0 :=
  RingEquiv.ofBijective (algebraMap K (homogeneousPieces K 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 2) K (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 2) K) ∈
          (1 : Submodule K (MvPolynomial (Fin 2) K)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

@[simp]
lemma coe_degreeZeroRingEquiv_apply (K : Type u) [Field K] (r : K) :
    ((degreeZeroRingEquiv K r : homogeneousPieces K 0) : MvPolynomial (Fin 2) K) =
      MvPolynomial.C r := rfl

private def coordinatePolynomialHom_genus_import_recovery_unit10 (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : MvPolynomial (Fin 2) K →+* F :=
  MvPolynomial.eval₂Hom ι fun i ↦ if i = 0 then g else 1

private lemma coordinatePolynomialHom_X_zero_genus_import_recovery_unit10 (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom_genus_import_recovery_unit10 K F ι g (MvPolynomial.X (0 : Fin 2)) = g := by
  simp [coordinatePolynomialHom_genus_import_recovery_unit10]

private lemma coordinatePolynomialHom_X_one_genus_import_recovery_unit10 (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom_genus_import_recovery_unit10 K F ι g (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinatePolynomialHom_genus_import_recovery_unit10]

/-- The affine-chart coordinate homomorphism sending `X₀ / X₁` to `g`. -/
private noncomputable def affineCoordinateRingHom_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+* F :=
  (Localization.awayLift (coordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [coordinatePolynomialHom_X_one_genus_import_recovery_unit10]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma affineCoordinateRingHom_affineCoordinateAway_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g (affineCoordinateAway K) = g := by
  simp only [affineCoordinateRingHom_genus_import_recovery_unit10, RingHom.comp_apply, affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk (coordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [coordinatePolynomialHom_X_one_genus_import_recovery_unit10]; simp) 1
  simpa [coordinatePolynomialHom_genus_import_recovery_unit10] using h

private def inverseCoordinatePolynomialHom_genus_import_recovery_unit10 (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : MvPolynomial (Fin 2) K →+* F :=
  MvPolynomial.eval₂Hom ι fun i ↦ if i = 1 then g else 1

private lemma inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseCoordinatePolynomialHom_genus_import_recovery_unit10 K F ι g (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit10]

private lemma inverseCoordinatePolynomialHom_X_one_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseCoordinatePolynomialHom_genus_import_recovery_unit10 K F ι g (MvPolynomial.X (1 : Fin 2)) = g := by
  simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit10]

private noncomputable def inverseAffineCoordinateRingHom_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →+* F :=
  (Localization.awayLift (inverseCoordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit10]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

private lemma inverseAffineCoordinateRingHom_inverseAffineCoordinateAway_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g (inverseAffineCoordinateAway K) = g := by
  simp only [inverseAffineCoordinateRingHom_genus_import_recovery_unit10, RingHom.comp_apply, inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk (inverseCoordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit10]; simp) 1
  simpa [inverseCoordinatePolynomialHom_genus_import_recovery_unit10] using h

private lemma basicOpenIsoSpec_hom_appTop_affineCoordinateAway_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) =
      (standardAffineOpen K).topIso.inv (affineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (standardAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K))) =
    (standardAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (affineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_affineCoordinate_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).inv.appTop
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  change e.inv.appTop ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_affineCoordinateAway_genus_import_recovery_unit10 K).symm

private lemma awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ standardAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_affineCoordinate_genus_import_recovery_unit10 (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  have hres : φ.resLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (standardAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (standardAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((standardAffineOpen K).topIso.inv (affineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge) (affineCoordinate K)) =
      (φ.resLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge).app ⊤
        ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge) (affineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge)
            ((standardAffineOpen K).topIso.hom
              ((standardAffineOpen K).topIso.inv (affineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
            (affineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_affineCoordinate_genus_import_recovery_unit10]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

private lemma basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) =
      (infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (infinityAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K))) =
    (infinityAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (inverseAffineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).inv.appTop
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  change e.inv.appTop ((infinityAffineOpen K).topIso.inv
    (inverseAffineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway_genus_import_recovery_unit10 K).symm

private lemma awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_inverseAffineCoordinate_genus_import_recovery_unit10 (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  have hres : φ.resLE (infinityAffineOpen K) ⊤
      (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (infinityAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (infinityAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge) (inverseAffineCoordinate K)) =
      (φ.resLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge).app ⊤
        ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge) (inverseAffineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge)
            ((infinityAffineOpen K).topIso.hom
              ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
            (inverseAffineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate_genus_import_recovery_unit10]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

/-- The `F`-valued point `[g : 1]` of the projective line associated to a field map `K → F`
and an element `g : F`.

For a curve function field, this is the generic-point morphism defined by the corresponding
rational function. The explicit field map makes the base-field structure part of the data and
avoids choosing a global `Algebra K F` instance. -/
noncomputable def ofElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)) ≫
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10

/-- The `F`-valued point `[1 : g]` of the projective line associated to a field map `K → F`
and an element `g : F`. -/
noncomputable def ofInverseElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)) ≫
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10

/-- The point `[1 : g]` lies in the affine chart `D₊(X₀)` containing infinity. -/
@[simp]
lemma ofInverseElement_preimage_basicOpen_X_zero
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    ofInverseElement K F ι g ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  rw [ofInverseElement, Scheme.Hom.comp_preimage]
  dsimp only [infinityAffineOpen]
  rw [
    ← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10]
  simp

/-- The point `[g : 1]` lies in the standard affine chart where the second homogeneous
coordinate is nonzero. -/
@[simp]
lemma ofElement_preimage_basicOpen_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤ := by
  rw [ofElement, Scheme.Hom.comp_preimage,
    ← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10]
  simp

/-- If `g` is nonzero, the point `[g : 1]` also lies in the affine chart `D₊(X₀)` containing
infinity. -/
lemma ofElement_preimage_basicOpen_X_zero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    ofElement K F ι g ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  rw [ofElement, Scheme.Hom.comp_preimage]
  dsimp only [infinityAffineOpen]
  have haway :
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
          (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (X_one_mem_degree_one K) (X_zero_mem_degree_one K)) :=
    Proj.awayι_preimage_basicOpen (𝒜 := homogeneousPieces K)
      (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10
  change Spec.map (CommRingCat.ofHom (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)) ⁻¹ᵁ
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10 ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))) = ⊤
  rw [haway]
  rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (X_one_mem_degree_one K) (X_zero_mem_degree_one K) = affineCoordinateAway K := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, affineCoordinateAway,
      HomogeneousLocalization.Away.val_mk]
  rw [helem]
  have hcoord : (CommRingCat.ofHom (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g))
      (affineCoordinateAway K) = g :=
    affineCoordinateRingHom_affineCoordinateAway_genus_import_recovery_unit10 K F ι g
  rw [hcoord]
  have hbasic : PrimeSpectrum.basicOpen g =
      (⊤ : TopologicalSpace.Opens (PrimeSpectrum F)) := by
    ext p
    change (g ∉ p.asIdeal) ↔ True
    rw [Ideal.eq_bot_of_prime p.asIdeal]
    simp [hg]
  exact hbasic

private lemma inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_one_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) from rfl)
        (inverseAffineCoordinateAway K) *
      HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_zero_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) from mul_comm _ _)
        (affineCoordinateAway K) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    inverseAffineCoordinateAway, affineCoordinateAway,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

private abbrev affineOverlapOpen_genus_import_recovery_unit10 (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

private lemma affineOverlapOpen_le_infinityAffineOpen_genus_import_recovery_unit10 (K : Type u) [Field K] :
    affineOverlapOpen_genus_import_recovery_unit10 K ≤ infinityAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (1 : Fin 2), rfl⟩

private lemma affineOverlapOpen_le_standardAffineOpen_genus_import_recovery_unit10 (K : Type u) [Field K] :
    affineOverlapOpen_genus_import_recovery_unit10 K ≤ standardAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (0 : Fin 2), mul_comm _ _⟩

private lemma inverseAffineCoordinate_mul_affineCoordinate_on_overlap_genus_import_recovery_unit10
    (K : Type u) [Field K] :
    (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen_genus_import_recovery_unit10 K)).op
        (inverseAffineCoordinate K) *
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen_genus_import_recovery_unit10 K)).op
        (affineCoordinate K) = 1 := by
  change ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen_genus_import_recovery_unit10 K)).op)
        (inverseAffineCoordinateAway K)) *
    ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen_genus_import_recovery_unit10 K)).op)
        (affineCoordinateAway K)) = 1
  rw [← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_one_mem_degree_one K) rfl,
    ← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_zero_mem_degree_one K) (mul_comm _ _)]
  change (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_one_mem_degree_one K) rfl (inverseAffineCoordinateAway K)) *
    (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_zero_mem_degree_one K) (mul_comm _ _) (affineCoordinateAway K)) = 1
  rw [← map_mul, inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap_genus_import_recovery_unit10, map_one]

private lemma ofElement_preimage_affineOverlapOpen_genus_import_recovery_unit10
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    ofElement K F ι g ⁻¹ᵁ affineOverlapOpen_genus_import_recovery_unit10 K = ⊤ := by
  rw [affineOverlapOpen_genus_import_recovery_unit10, Proj.basicOpen_mul, Scheme.Hom.preimage_inf,
    ofElement_preimage_basicOpen_X_zero K F ι g hg,
    ofElement_preimage_basicOpen_X_one, inf_top_eq]

/-- Pulling the standard affine coordinate `X₀ / X₁` back along `[g : 1]` gives `g`.

This is the computational interface needed to distinguish the rational-function morphism of a
non-global function from a constant morphism. -/
lemma ofElement_appLE_affineCoordinate (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    (ofElement K F ι g).appLE (standardAffineOpen K) ⊤
        (ofElement_preimage_basicOpen_X_one K F ι g).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g := by
  change ((Spec.map (CommRingCat.ofHom (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).appLE
      (standardAffineOpen K) ⊤ (ofElement_preimage_basicOpen_X_one K F ι g).ge)
        (affineCoordinate K) = _
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)))
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10)
    (standardAffineOpen K) ⊤ ⊤ (awayι_preimage_standardAffineOpen_genus_import_recovery_unit10 K).ge le_rfl]
  simp only [CommRingCat.comp_apply, awayι_appLE_affineCoordinate_genus_import_recovery_unit10]
  change (((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv ≫
        (Spec.map (CommRingCat.ofHom
          (affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g))).appTop) (affineCoordinateAway K)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (Scheme.ΓSpecIso (.of F)).inv
    (affineCoordinateRingHom_affineCoordinateAway_genus_import_recovery_unit10 K F ι g)

/-- Pulling the inverse affine coordinate `X₁ / X₀` back along `[1 : g]` gives `g`. -/
lemma ofInverseElement_appLE_inverseAffineCoordinate
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    (ofInverseElement K F ι g).appLE (infinityAffineOpen K) ⊤
        (ofInverseElement_preimage_basicOpen_X_zero K F ι g).ge
        (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g := by
  change ((Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10).appLE
      (infinityAffineOpen K) ⊤
        (ofInverseElement_preimage_basicOpen_X_zero K F ι g).ge)
          (inverseAffineCoordinate K) = _
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g)))
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit10)
    (infinityAffineOpen K) ⊤ ⊤ (awayι_preimage_infinityAffineOpen_genus_import_recovery_unit10 K).ge le_rfl]
  simp only [CommRingCat.comp_apply, awayι_appLE_inverseAffineCoordinate_genus_import_recovery_unit10]
  change (((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv ≫
        (Spec.map (CommRingCat.ofHom
          (inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g))).appTop)
        (inverseAffineCoordinateAway K)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (Scheme.ΓSpecIso (.of F)).inv
    (inverseAffineCoordinateRingHom_inverseAffineCoordinateAway_genus_import_recovery_unit10 K F ι g)

/-- Pulling the inverse affine coordinate `X₁ / X₀` back along a nonzero point `[g : 1]`
gives `g⁻¹`. -/
lemma ofElement_appLE_inverseAffineCoordinate
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    (ofElement K F ι g).appLE (infinityAffineOpen K) ⊤
        (ofElement_preimage_basicOpen_X_zero K F ι g hg).ge
        (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g⁻¹ := by
  let φ := ofElement K F ι g
  let W := affineOverlapOpen_genus_import_recovery_unit10 K
  have hW : φ ⁻¹ᵁ W = ⊤ := ofElement_preimage_affineOverlapOpen_genus_import_recovery_unit10 K F ι g hg
  have hInf : φ ⁻¹ᵁ infinityAffineOpen K = ⊤ :=
    ofElement_preimage_basicOpen_X_zero K F ι g hg
  have hStd : φ ⁻¹ᵁ standardAffineOpen K = ⊤ :=
    ofElement_preimage_basicOpen_X_one K F ι g
  have hInfPull :
      φ.appLE W ⊤ hW.ge
          ((scheme K).presheaf.map
            (homOfLE (affineOverlapOpen_le_infinityAffineOpen_genus_import_recovery_unit10 K)).op
            (inverseAffineCoordinate K)) =
        φ.appLE (infinityAffineOpen K) ⊤ hInf.ge
          (inverseAffineCoordinate K) := by
    change (((scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen_genus_import_recovery_unit10 K)).op ≫
      φ.appLE W ⊤ hW.ge) (inverseAffineCoordinate K)) = _
    rw [Scheme.Hom.map_appLE]
  have hStdPull :
      φ.appLE W ⊤ hW.ge
          ((scheme K).presheaf.map
            (homOfLE (affineOverlapOpen_le_standardAffineOpen_genus_import_recovery_unit10 K)).op
            (affineCoordinate K)) =
        φ.appLE (standardAffineOpen K) ⊤ hStd.ge (affineCoordinate K) := by
    change (((scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen_genus_import_recovery_unit10 K)).op ≫
      φ.appLE W ⊤ hW.ge) (affineCoordinate K)) = _
    rw [Scheme.Hom.map_appLE]
  have hprod := congrArg (φ.appLE W ⊤ hW.ge)
    (inverseAffineCoordinate_mul_affineCoordinate_on_overlap_genus_import_recovery_unit10 K)
  simp only [map_mul, map_one] at hprod
  rw [hInfPull, hStdPull] at hprod
  have hcoord :
      φ.appLE (standardAffineOpen K) ⊤ hStd.ge (affineCoordinate K) =
        (Scheme.ΓSpecIso (.of F)).inv g := by
    exact ofElement_appLE_affineCoordinate K F ι g
  rw [hcoord] at hprod
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of F)).hom).1
  rw [Iso.inv_hom_id_apply]
  have hprodF := congrArg (Scheme.ΓSpecIso (.of F)).hom hprod
  simp only [map_mul, Iso.inv_hom_id_apply, map_one] at hprodF
  apply mul_right_cancel₀ hg
  rw [hprodF, inv_mul_cancel₀ hg]

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[g : 1]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofElement, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change affineCoordinateRingHom_genus_import_recovery_unit10 K F ι g
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) (degreeZeroRingEquiv K r)) = ι r
  simp only [affineCoordinateRingHom_genus_import_recovery_unit10, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk (coordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [coordinatePolynomialHom_X_one_genus_import_recovery_unit10]; simp) 0
  convert h using 1
  · congr 1
  · simp [coordinatePolynomialHom_genus_import_recovery_unit10]

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[1 : g]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofInverseElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofInverseElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofInverseElement, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change inverseAffineCoordinateRingHom_genus_import_recovery_unit10 K F ι g
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2))) (degreeZeroRingEquiv K r)) = ι r
  simp only [inverseAffineCoordinateRingHom_genus_import_recovery_unit10, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk (inverseCoordinatePolynomialHom_genus_import_recovery_unit10 K F ι g)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit10]; simp) 0
  convert h using 1
  · congr 1
  · simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit10]

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti

end


section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# The structure morphism of the projective line

This file equips `ProjectiveLine.scheme K` with its structure morphism to `Spec K`. It identifies
the degree-zero part of `K[X₀, X₁]` with `K`, verifies finite generation over that degree-zero
part, and records that the structure morphism is locally of finite type and proper.

These are prerequisites for spreading a function-field point out to a rational map and then
extending it on a proper regular curve, as required by the product formula in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/


open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace ProjectiveLine

noncomputable section

/-- The homogeneous coordinate ring of the projective line is finitely generated over its
degree-zero part. -/
noncomputable instance (K : Type u) [Field K] :
    Algebra.FiniteType (homogeneousPieces K 0) (MvPolynomial (Fin 2) K) := by
  letI : IsScalarTower K (homogeneousPieces K 0) (MvPolynomial (Fin 2) K) :=
    IsScalarTower.of_algebraMap_eq
      (R := K) (S := homogeneousPieces K 0) (A := MvPolynomial (Fin 2) K)
      (fun r ↦ by rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    K (homogeneousPieces K 0) (MvPolynomial (Fin 2) K)

/-- The structure morphism `ℙ¹_K ⟶ Spec K`. -/
@[expose]
noncomputable def structureMap (K : Type u) [Field K] : scheme K ⟶ Spec (.of K) :=
  Proj.toSpecZero (homogeneousPieces K) ≫
    Spec.map (degreeZeroRingEquiv K).toCommRingCatIso.hom

/-- The point `[g : 1]` lies over the base-field map `K → F`. -/
@[reassoc]
lemma ofElement_comp_structureMap (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ structureMap K =
      Spec.map (CommRingCat.ofHom ι) := by
  rw [structureMap, ← Category.assoc, ofElement_toSpecZero]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

/-- The point `[1 : g]` lies over the base-field map `K → F`. -/
@[reassoc]
lemma ofInverseElement_comp_structureMap (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofInverseElement K F ι g ≫ structureMap K =
      Spec.map (CommRingCat.ofHom ι) := by
  rw [structureMap, ← Category.assoc, ofInverseElement_toSpecZero]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

noncomputable instance (K : Type u) [Field K] :
    LocallyOfFiniteType (structureMap K) := by
  dsimp only [structureMap]
  infer_instance

noncomputable instance (K : Type u) [Field K] : IsProper (structureMap K) := by
  dsimp only [structureMap]
  infer_instance

/-- The structure morphism of the projective line satisfies the valuative criterion. -/
lemma structureMap_valuativeCriterion (K : Type u) [Field K] :
    ValuativeCriterion (structureMap K) := by
  have h : IsProper (structureMap K) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti

end


section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# Smoothness and integrality of the projective line

This file identifies both standard affine charts of the projective line with a one-variable
polynomial ring. The explicit presentations prove that the structure morphism is smooth of
relative dimension one. The same charts, together with the homogeneous zero ideal, show that
the projective line is integral; properness and finite type then imply it is Noetherian.

These instances are the target-side geometric input for the finite morphism used in the
product-formula proof.
-/


open scoped DirectSum
open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.ProjectiveLine

universe u

noncomputable section

private noncomputable def t_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

private lemma adjoin_X_over_degreeZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) = ⊤ := by
  apply top_unique
  intro p _
  have hall : ∀ p : MvPolynomial (Fin 2) K,
      p ∈ Algebra.adjoin (homogeneousPieces K 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r =>
        have h := (Algebra.adjoin (homogeneousPieces K 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K))).algebraMap_mem
          (degreeZeroRingEquiv K r)
        simpa using h
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact hall p

private lemma adjoin_t_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0) ({t_genus_import_recovery_unit12 K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_one_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero_genus_import_recovery_unit12 K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX1 : MvPolynomial.X (1 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (1 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (1 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
        (MvPolynomial.X (1 : Fin 2))
        ⟨MvPolynomial.X (1 : Fin 2), hX1⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
          hX1
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t_genus_import_recovery_unit12 K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t_genus_import_recovery_unit12, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t_genus_import_recovery_unit12 K))
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t_genus_import_recovery_unit12 K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t_genus_import_recovery_unit12, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t_genus_import_recovery_unit12 K))

private def coordinateToPolynomialHom_genus_import_recovery_unit12 (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 0 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHom_X_zero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    coordinateToPolynomialHom_genus_import_recovery_unit12 K (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHom_genus_import_recovery_unit12]

private lemma coordinateToPolynomialHom_X_one_genus_import_recovery_unit12 (K : Type u) [Field K] :
    coordinateToPolynomialHom_genus_import_recovery_unit12 K (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHom_genus_import_recovery_unit12]

private noncomputable def awayToPolynomial_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHom_genus_import_recovery_unit12 K)
      (MvPolynomial.X (1 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHom_genus_import_recovery_unit12 K (MvPolynomial.X (1 : Fin 2)))
        rw [coordinateToPolynomialHom_X_one_genus_import_recovery_unit12]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma awayToPolynomial_t_genus_import_recovery_unit12 (K : Type u) [Field K] :
    awayToPolynomial_genus_import_recovery_unit12 K (t_genus_import_recovery_unit12 K) = Polynomial.X := by
  simp only [awayToPolynomial_genus_import_recovery_unit12, RingHom.comp_apply, t_genus_import_recovery_unit12,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHom_genus_import_recovery_unit12 K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one_genus_import_recovery_unit12]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom_genus_import_recovery_unit12 K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    hinv 1
  simpa [coordinateToPolynomialHom_genus_import_recovery_unit12] using h

private lemma awayToPolynomial_fromZero_genus_import_recovery_unit12 (K : Type u) [Field K]
    (r : homogeneousPieces K 0) :
    awayToPolynomial_genus_import_recovery_unit12 K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomial_genus_import_recovery_unit12, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHom_genus_import_recovery_unit12 K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one_genus_import_recovery_unit12]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom_genus_import_recovery_unit12 K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C s) 1
    hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHom_genus_import_recovery_unit12]

private noncomputable def awayToPolynomialAlgHom_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomial_genus_import_recovery_unit12 K with
    commutes' := awayToPolynomial_fromZero_genus_import_recovery_unit12 K }

private lemma transcendental_t_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Transcendental (homogeneousPieces K 0) (t_genus_import_recovery_unit12 K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) hpq
  have ht : (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (t_genus_import_recovery_unit12 K) = Polynomial.X :=
    awayToPolynomial_t_genus_import_recovery_unit12 K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (t_genus_import_recovery_unit12 K)) p := by
      rw [ht]
    _ = (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (Polynomial.aeval (t_genus_import_recovery_unit12 K) p) :=
      AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (t_genus_import_recovery_unit12 K)) p
    _ = (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (Polynomial.aeval (t_genus_import_recovery_unit12 K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (t_genus_import_recovery_unit12 K)) q :=
      (AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom_genus_import_recovery_unit12 K) (t_genus_import_recovery_unit12 K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayAlgEquiv_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (t_genus_import_recovery_unit12 K)
    (transcendental_t_genus_import_recovery_unit12 K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_t_genus_import_recovery_unit12 K)).trans Subalgebra.topEquiv)

/-- The standard affine chart of the projective line is a polynomial line over the degree-zero
homogeneous coordinate ring. -/
noncomputable def standardAffinePolynomialEquiv (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃+*
      Γ(scheme K, standardAffineOpen K) :=
  (polynomialAwayAlgEquiv_genus_import_recovery_unit12 K).toRingEquiv.trans
    (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).commRingCatIsoToRingEquiv

/-- Under the polynomial presentation of the standard chart, the polynomial variable is the
affine coordinate `X₀ / X₁`. -/
@[simp]
lemma standardAffinePolynomialEquiv_X (K : Type u) [Field K] :
    standardAffinePolynomialEquiv K Polynomial.X = affineCoordinate K := by
  change (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).hom
        (polynomialAwayAlgEquiv_genus_import_recovery_unit12 K Polynomial.X) = _
  have hX : polynomialAwayAlgEquiv_genus_import_recovery_unit12 K Polynomial.X = t_genus_import_recovery_unit12 K := by
    simp [polynomialAwayAlgEquiv_genus_import_recovery_unit12]
  rw [hX]
  congr 1

/-- The standard affine coordinate on `ℙ¹` is nonzero. -/
lemma affineCoordinate_ne_zero (K : Type u) [Field K] :
    affineCoordinate K ≠ 0 := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  intro h
  have hX : (Polynomial.X : Polynomial (homogeneousPieces K 0)) = 0 := by
    apply (standardAffinePolynomialEquiv K).injective
    simpa only [standardAffinePolynomialEquiv_X, map_zero] using h
  exact Polynomial.X_ne_zero hX

/-- The standard chart `D₊(X₁)` is affine. -/
lemma isAffineOpen_standardAffineOpen (K : Type u) [Field K] :
    IsAffineOpen (standardAffineOpen K) :=
  Proj.isAffineOpen_basicOpen (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X (1 : Fin 2))
    (f_deg := X_one_mem_degree_one K) (hm := Nat.zero_lt_one)

/-- The two standard affine charts cover the projective line. -/
lemma standardAffineOpen_sup_infinityAffineOpen_eq_top
    (K : Type u) [Field K] :
    standardAffineOpen K ⊔ infinityAffineOpen K = ⊤ := by
  have hcover : ⨆ i : Fin 2,
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero_genus_import_recovery_unit12 K)
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_right
  · exact le_sup_left

/-- The zero locus of the affine coordinate is a prime point of the standard chart. -/
theorem span_affineCoordinate_isPrime (K : Type u) [Field K] :
    (Ideal.span ({affineCoordinate K} : Set
      Γ(scheme K, standardAffineOpen K))).IsPrime := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  let e := standardAffinePolynomialEquiv K
  have hprimeX : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsPrime := by
    rw [← Polynomial.ker_constantCoeff]
    exact RingHom.ker_isPrime _
  letI : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsPrime := hprimeX
  have hmap : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).map e =
        Ideal.span ({affineCoordinate K} : Set
          Γ(scheme K, standardAffineOpen K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg Ideal.span (Set.singleton_eq_singleton_iff.mpr
      (standardAffinePolynomialEquiv_X K))
  rw [← hmap]
  infer_instance

/-- The zero locus of the affine coordinate is a maximal point of the standard chart. -/
theorem span_affineCoordinate_isMaximal (K : Type u) [Field K] :
    (Ideal.span ({affineCoordinate K} : Set
      Γ(scheme K, standardAffineOpen K))).IsMaximal := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  let e := standardAffinePolynomialEquiv K
  have hmaxX : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsMaximal := by
    rw [← Polynomial.ker_constantCoeff]
    exact RingHom.ker_isMaximal_of_surjective _ Polynomial.constantCoeff_surjective
  letI : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsMaximal := hmaxX
  have hmap : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).map e =
        Ideal.span ({affineCoordinate K} : Set
          Γ(scheme K, standardAffineOpen K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg Ideal.span (Set.singleton_eq_singleton_iff.mpr
      (standardAffinePolynomialEquiv_X K))
  rw [← hmap]
  infer_instance

/-- The prime of the standard affine chart cut out by its coordinate. -/
@[expose] noncomputable def zeroPrime (K : Type u) [Field K] :
    PrimeSpectrum Γ(scheme K, standardAffineOpen K) :=
  ⟨Ideal.span ({affineCoordinate K} : Set
    Γ(scheme K, standardAffineOpen K)), span_affineCoordinate_isPrime K⟩

@[simp]
lemma zeroPrime_asIdeal (K : Type u) [Field K] :
    (zeroPrime K).asIdeal = Ideal.span ({affineCoordinate K} : Set
      Γ(scheme K, standardAffineOpen K)) := rfl

/-- The zero point `[0 : 1]` of the projective line, defined through the standard affine chart. -/
noncomputable def zeroPoint (K : Type u) [Field K] : scheme K :=
  (isAffineOpen_standardAffineOpen K).fromSpec (zeroPrime K)

/-- The zero point belongs to the standard affine chart. -/
lemma zeroPoint_mem_standardAffineOpen (K : Type u) [Field K] :
    zeroPoint K ∈ standardAffineOpen K := by
  let hU := isAffineOpen_standardAffineOpen K
  let q : Spec Γ(scheme K, standardAffineOpen K) := zeroPrime K
  have hmem : hU.fromSpec q ∈ Set.range hU.fromSpec := Set.mem_range_self q
  rw [hU.range_fromSpec] at hmem
  simpa [zeroPoint, q] using hmem

/-- In the standard affine chart, the prime ideal of the zero point is generated by the affine
coordinate. -/
lemma primeIdealOf_zeroPoint (K : Type u) [Field K] :
    (isAffineOpen_standardAffineOpen K).primeIdealOf
        ⟨zeroPoint K, zeroPoint_mem_standardAffineOpen K⟩ = zeroPrime K := by
  let hU := isAffineOpen_standardAffineOpen K
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  rfl

@[simp]
lemma primeIdealOf_zeroPoint_asIdeal (K : Type u) [Field K] :
    ((isAffineOpen_standardAffineOpen K).primeIdealOf
      ⟨zeroPoint K, zeroPoint_mem_standardAffineOpen K⟩).asIdeal =
        Ideal.span ({affineCoordinate K} : Set
          Γ(scheme K, standardAffineOpen K)) := by
  rw [primeIdealOf_zeroPoint, zeroPrime_asIdeal]

@[simp]
lemma primeIdealOf_zeroPoint_asIdeal_of_mem (K : Type u) [Field K]
    (hz : zeroPoint K ∈ standardAffineOpen K) :
    ((isAffineOpen_standardAffineOpen K).primeIdealOf ⟨zeroPoint K, hz⟩).asIdeal =
      Ideal.span ({affineCoordinate K} : Set
        Γ(scheme K, standardAffineOpen K)) := by
  simpa only [Subsingleton.elim hz (zeroPoint_mem_standardAffineOpen K)] using
    primeIdealOf_zeroPoint_asIdeal K

/-- A point of the standard chart contains the affine coordinate in its prime ideal exactly
when it is the zero point. -/
lemma affineCoordinate_mem_primeIdealOf_iff_eq_zeroPoint
    (K : Type u) [Field K] (y : scheme K) (hy : y ∈ standardAffineOpen K) :
    affineCoordinate K ∈
        ((isAffineOpen_standardAffineOpen K).primeIdealOf ⟨y, hy⟩).asIdeal ↔
      y = zeroPoint K := by
  let hU := isAffineOpen_standardAffineOpen K
  constructor
  · intro ht
    have ht' : affineCoordinate K ∈
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
      simpa [hU] using ht
    have hle : Ideal.span ({affineCoordinate K} : Set
        Γ(scheme K, standardAffineOpen K)) ≤
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
      Ideal.span_le.mpr (by
        intro z hz
        have hz' : z = affineCoordinate K := Set.mem_singleton_iff.mp hz
        subst z
        change affineCoordinate K ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal
        exact ht')
    have heq : Ideal.span ({affineCoordinate K} : Set
        Γ(scheme K, standardAffineOpen K)) =
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
      (span_affineCoordinate_isMaximal K).eq_of_le
        (hU.primeIdealOf ⟨y, hy⟩).isPrime.ne_top hle
    have hprime : hU.primeIdealOf ⟨y, hy⟩ = zeroPrime K := by
      apply PrimeSpectrum.ext
      exact heq.symm.trans (zeroPrime_asIdeal K).symm
    calc
      y = hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) :=
        (hU.fromSpec_primeIdealOf ⟨y, hy⟩).symm
      _ = hU.fromSpec (zeroPrime K) := congrArg hU.fromSpec hprime
      _ = zeroPoint K := rfl
  · rintro rfl
    rw [primeIdealOf_zeroPoint_asIdeal_of_mem]
    exact Ideal.subset_span (Set.mem_singleton _)

private noncomputable def mvPolynomialPresentation_genus_import_recovery_unit12 (R : Type u) [CommRing R] :
    Algebra.Presentation R (MvPolynomial Unit R) Unit Empty where
  toGenerators := Algebra.Generators.mvPolynomial R Unit
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact Algebra.Generators.ker_mvPolynomial.symm

private noncomputable def mvPolynomialPreSubmersivePresentation_genus_import_recovery_unit12
    (R : Type u) [CommRing R] :
    Algebra.PreSubmersivePresentation R (MvPolynomial Unit R) Unit Empty where
  toPresentation := mvPolynomialPresentation_genus_import_recovery_unit12 R
  map := Empty.elim
  map_inj a := Empty.elim a

private noncomputable def mvPolynomialSubmersivePresentation_genus_import_recovery_unit12
    (R : Type u) [CommRing R] :
    Algebra.SubmersivePresentation R (MvPolynomial Unit R) Unit Empty where
  toPreSubmersivePresentation := mvPolynomialPreSubmersivePresentation_genus_import_recovery_unit12 R
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

private lemma mvPolynomial_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) := by
  apply (mvPolynomialSubmersivePresentation_genus_import_recovery_unit12 R).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

private lemma polynomial_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) :=
    mvPolynomial_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 R
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv R Unit)

private lemma away_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12
    (K : Type u) [Field K] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 (homogeneousPieces K 0)
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      (homogeneousPieces K 0) (Polynomial (homogeneousPieces K 0)) :=
    polynomial_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 (homogeneousPieces K 0)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (S := Polynomial (homogeneousPieces K 0)) 1
    (polynomialAwayAlgEquiv_genus_import_recovery_unit12 K)

private noncomputable def tZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

private lemma adjoin_tZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Algebra.adjoin (homogeneousPieces K 0) ({tZero_genus_import_recovery_unit12 K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_zero_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero_genus_import_recovery_unit12 K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero_genus_import_recovery_unit12 K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero_genus_import_recovery_unit12,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero_genus_import_recovery_unit12 K))
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX0 : MvPolynomial.X (0 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (0 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (0 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2))))
        (MvPolynomial.X (0 : Fin 2)) ⟨MvPolynomial.X (0 : Fin 2), hX0⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))) hX0
    rw [heq]
    exact one_mem _
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero_genus_import_recovery_unit12 K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero_genus_import_recovery_unit12,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero_genus_import_recovery_unit12 K))

private def coordinateToPolynomialHomZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 1 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHomZero_X_zero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    coordinateToPolynomialHomZero_genus_import_recovery_unit12 K (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHomZero_genus_import_recovery_unit12]

private lemma coordinateToPolynomialHomZero_X_one_genus_import_recovery_unit12 (K : Type u) [Field K] :
    coordinateToPolynomialHomZero_genus_import_recovery_unit12 K (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHomZero_genus_import_recovery_unit12]

private noncomputable def awayToPolynomialZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHomZero_genus_import_recovery_unit12 K)
      (MvPolynomial.X (0 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHomZero_genus_import_recovery_unit12 K (MvPolynomial.X (0 : Fin 2)))
        rw [coordinateToPolynomialHomZero_X_zero_genus_import_recovery_unit12]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

private lemma awayToPolynomialZero_tZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    awayToPolynomialZero_genus_import_recovery_unit12 K (tZero_genus_import_recovery_unit12 K) = Polynomial.X := by
  simp only [awayToPolynomialZero_genus_import_recovery_unit12, RingHom.comp_apply, tZero_genus_import_recovery_unit12,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHomZero_genus_import_recovery_unit12 K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero_genus_import_recovery_unit12]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero_genus_import_recovery_unit12 K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1 hinv 1
  simpa [coordinateToPolynomialHomZero_genus_import_recovery_unit12] using h

private lemma awayToPolynomialZero_fromZero_genus_import_recovery_unit12 (K : Type u) [Field K]
    (r : homogeneousPieces K 0) :
    awayToPolynomialZero_genus_import_recovery_unit12 K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomialZero_genus_import_recovery_unit12, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHomZero_genus_import_recovery_unit12 K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero_genus_import_recovery_unit12]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero_genus_import_recovery_unit12 K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C s) 1 hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHomZero_genus_import_recovery_unit12]

private noncomputable def awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 (K : Type u) [Field K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomialZero_genus_import_recovery_unit12 K with
    commutes' := awayToPolynomialZero_fromZero_genus_import_recovery_unit12 K }

private lemma transcendental_tZero_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Transcendental (homogeneousPieces K 0) (tZero_genus_import_recovery_unit12 K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) hpq
  have ht : (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (tZero_genus_import_recovery_unit12 K) = Polynomial.X :=
    awayToPolynomialZero_tZero_genus_import_recovery_unit12 K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (tZero_genus_import_recovery_unit12 K)) p := by rw [ht]
    _ = (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (Polynomial.aeval (tZero_genus_import_recovery_unit12 K) p) :=
      AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (tZero_genus_import_recovery_unit12 K)) p
    _ = (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (Polynomial.aeval (tZero_genus_import_recovery_unit12 K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (tZero_genus_import_recovery_unit12 K)) q :=
      (AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom_genus_import_recovery_unit12 K) (tZero_genus_import_recovery_unit12 K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (tZero_genus_import_recovery_unit12 K)
    (transcendental_tZero_genus_import_recovery_unit12 K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_tZero_genus_import_recovery_unit12 K)).trans Subalgebra.topEquiv)

/-- The affine chart containing infinity is a polynomial line over the degree-zero homogeneous
coordinate ring. -/
noncomputable def infinityAffinePolynomialEquiv (K : Type u) [Field K] :
    Polynomial (homogeneousPieces K 0) ≃+*
      Γ(scheme K, infinityAffineOpen K) :=
  (polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 K).toRingEquiv.trans
    (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one).commRingCatIsoToRingEquiv

/-- Under the polynomial presentation of the chart at infinity, the polynomial variable is the
inverse affine coordinate `X₁ / X₀`. -/
@[simp]
lemma infinityAffinePolynomialEquiv_X (K : Type u) [Field K] :
    infinityAffinePolynomialEquiv K Polynomial.X = inverseAffineCoordinate K := by
  change (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one).hom
        (polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 K Polynomial.X) = _
  have hX : polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 K Polynomial.X = tZero_genus_import_recovery_unit12 K := by
    simp [polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12]
  rw [hX]
  congr 1

/-- The inverse affine coordinate on `ℙ¹` is nonzero. -/
lemma inverseAffineCoordinate_ne_zero (K : Type u) [Field K] :
    inverseAffineCoordinate K ≠ 0 := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  intro h
  have hX : (Polynomial.X : Polynomial (homogeneousPieces K 0)) = 0 := by
    apply (infinityAffinePolynomialEquiv K).injective
    simpa only [infinityAffinePolynomialEquiv_X, map_zero] using h
  exact Polynomial.X_ne_zero hX

/-- The chart `D₊(X₀)` containing infinity is affine. -/
lemma isAffineOpen_infinityAffineOpen (K : Type u) [Field K] :
    IsAffineOpen (infinityAffineOpen K) :=
  Proj.isAffineOpen_basicOpen (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X (0 : Fin 2))
    (f_deg := X_zero_mem_degree_one K) (hm := Nat.zero_lt_one)

/-- The zero locus of the inverse affine coordinate is a prime point of the chart at infinity. -/
theorem span_inverseAffineCoordinate_isPrime (K : Type u) [Field K] :
    (Ideal.span ({inverseAffineCoordinate K} : Set
      Γ(scheme K, infinityAffineOpen K))).IsPrime := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  let e := infinityAffinePolynomialEquiv K
  have hprimeX : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsPrime := by
    rw [← Polynomial.ker_constantCoeff]
    exact RingHom.ker_isPrime _
  letI : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsPrime := hprimeX
  have hmap : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).map e =
        Ideal.span ({inverseAffineCoordinate K} : Set
          Γ(scheme K, infinityAffineOpen K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg Ideal.span (Set.singleton_eq_singleton_iff.mpr
      (infinityAffinePolynomialEquiv_X K))
  rw [← hmap]
  infer_instance

/-- The zero locus of the inverse affine coordinate is a maximal point of the chart at
infinity. -/
theorem span_inverseAffineCoordinate_isMaximal (K : Type u) [Field K] :
    (Ideal.span ({inverseAffineCoordinate K} : Set
      Γ(scheme K, infinityAffineOpen K))).IsMaximal := by
  letI : Field (homogeneousPieces K 0) :=
    ((degreeZeroRingEquiv K).symm.toMulEquiv.isField (Field.toIsField K)).toField
  let e := infinityAffinePolynomialEquiv K
  have hmaxX : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsMaximal := by
    rw [← Polynomial.ker_constantCoeff]
    exact RingHom.ker_isMaximal_of_surjective _ Polynomial.constantCoeff_surjective
  letI : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).IsMaximal := hmaxX
  have hmap : (Ideal.span ({Polynomial.X} : Set
      (Polynomial (homogeneousPieces K 0)))).map e =
        Ideal.span ({inverseAffineCoordinate K} : Set
          Γ(scheme K, infinityAffineOpen K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg Ideal.span (Set.singleton_eq_singleton_iff.mpr
      (infinityAffinePolynomialEquiv_X K))
  rw [← hmap]
  infer_instance

/-- The prime of the affine chart at infinity cut out by the inverse coordinate. -/
@[expose] noncomputable def infinityPrime (K : Type u) [Field K] :
    PrimeSpectrum Γ(scheme K, infinityAffineOpen K) :=
  ⟨Ideal.span ({inverseAffineCoordinate K} : Set
    Γ(scheme K, infinityAffineOpen K)), span_inverseAffineCoordinate_isPrime K⟩

@[simp]
lemma infinityPrime_asIdeal (K : Type u) [Field K] :
    (infinityPrime K).asIdeal = Ideal.span ({inverseAffineCoordinate K} : Set
      Γ(scheme K, infinityAffineOpen K)) := rfl

/-- The point `[1 : 0]` of the projective line, defined through the affine chart at infinity. -/
noncomputable def infinityPoint (K : Type u) [Field K] : scheme K :=
  (isAffineOpen_infinityAffineOpen K).fromSpec (infinityPrime K)

/-- The point at infinity belongs to the chart `D₊(X₀)`. -/
lemma infinityPoint_mem_infinityAffineOpen (K : Type u) [Field K] :
    infinityPoint K ∈ infinityAffineOpen K := by
  let hU := isAffineOpen_infinityAffineOpen K
  let q : Spec Γ(scheme K, infinityAffineOpen K) := infinityPrime K
  have hmem : hU.fromSpec q ∈ Set.range hU.fromSpec := Set.mem_range_self q
  rw [hU.range_fromSpec] at hmem
  simpa [infinityPoint, q] using hmem

/-- In the chart at infinity, the prime ideal of `[1 : 0]` is generated by the inverse affine
coordinate. -/
lemma primeIdealOf_infinityPoint (K : Type u) [Field K] :
    (isAffineOpen_infinityAffineOpen K).primeIdealOf
        ⟨infinityPoint K, infinityPoint_mem_infinityAffineOpen K⟩ = infinityPrime K := by
  let hU := isAffineOpen_infinityAffineOpen K
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  rfl

@[simp]
lemma primeIdealOf_infinityPoint_asIdeal (K : Type u) [Field K] :
    ((isAffineOpen_infinityAffineOpen K).primeIdealOf
      ⟨infinityPoint K, infinityPoint_mem_infinityAffineOpen K⟩).asIdeal =
        Ideal.span ({inverseAffineCoordinate K} : Set
          Γ(scheme K, infinityAffineOpen K)) := by
  rw [primeIdealOf_infinityPoint, infinityPrime_asIdeal]

@[simp]
lemma primeIdealOf_infinityPoint_asIdeal_of_mem (K : Type u) [Field K]
    (hinf : infinityPoint K ∈ infinityAffineOpen K) :
    ((isAffineOpen_infinityAffineOpen K).primeIdealOf ⟨infinityPoint K, hinf⟩).asIdeal =
      Ideal.span ({inverseAffineCoordinate K} : Set
        Γ(scheme K, infinityAffineOpen K)) := by
  simpa only [Subsingleton.elim hinf (infinityPoint_mem_infinityAffineOpen K)] using
    primeIdealOf_infinityPoint_asIdeal K

/-- A point of the chart at infinity contains the inverse affine coordinate in its prime ideal
exactly when it is the point at infinity. -/
lemma inverseAffineCoordinate_mem_primeIdealOf_iff_eq_infinityPoint
    (K : Type u) [Field K] (y : scheme K) (hy : y ∈ infinityAffineOpen K) :
    inverseAffineCoordinate K ∈
        ((isAffineOpen_infinityAffineOpen K).primeIdealOf ⟨y, hy⟩).asIdeal ↔
      y = infinityPoint K := by
  let hU := isAffineOpen_infinityAffineOpen K
  constructor
  · intro ht
    have ht' : inverseAffineCoordinate K ∈
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
      simpa [hU] using ht
    have hle : Ideal.span ({inverseAffineCoordinate K} : Set
        Γ(scheme K, infinityAffineOpen K)) ≤
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
      Ideal.span_le.mpr (by
        intro z hz
        have hz' : z = inverseAffineCoordinate K := Set.mem_singleton_iff.mp hz
        subst z
        change inverseAffineCoordinate K ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal
        exact ht')
    have heq : Ideal.span ({inverseAffineCoordinate K} : Set
        Γ(scheme K, infinityAffineOpen K)) =
        (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
      (span_inverseAffineCoordinate_isMaximal K).eq_of_le
        (hU.primeIdealOf ⟨y, hy⟩).isPrime.ne_top hle
    have hprime : hU.primeIdealOf ⟨y, hy⟩ = infinityPrime K := by
      apply PrimeSpectrum.ext
      exact heq.symm.trans (infinityPrime_asIdeal K).symm
    calc
      y = hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) :=
        (hU.fromSpec_primeIdealOf ⟨y, hy⟩).symm
      _ = hU.fromSpec (infinityPrime K) := congrArg hU.fromSpec hprime
      _ = infinityPoint K := rfl
  · rintro rfl
    rw [primeIdealOf_infinityPoint_asIdeal_of_mem]
    exact Ideal.subset_span (Set.mem_singleton _)

private lemma away_zero_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12
    (K : Type u) [Field K] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 (homogeneousPieces K 0)
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      (homogeneousPieces K 0) (Polynomial (homogeneousPieces K 0)) :=
    polynomial_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 (homogeneousPieces K 0)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (S := Polynomial (homogeneousPieces K 0)) 1
    (polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 K)

private lemma chartRingHom_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12
    (K : Type u) [Field K] (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X i))).comp
          (degreeZeroRingEquiv K).toRingHom) := by
  have hBase : RingHom.IsStandardSmoothOfRelativeDimension 0
      (degreeZeroRingEquiv K).toRingHom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (degreeZeroRingEquiv K)
  have hAway : RingHom.IsStandardSmoothOfRelativeDimension 1
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X i))) := by
    fin_cases i
    · exact away_zero_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 K
    · exact away_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 K
  simpa using hAway.comp hBase

noncomputable instance (K : Type u) [Field K] :
    SmoothOfRelativeDimension 1 (structureMap K) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally (@SmoothOfRelativeDimension 1)]
    exact affineLocally_respectsIso _
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension 1)).respectsIso
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1)
    (fun i : Fin 2 ↦ Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i))
    (Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero_genus_import_recovery_unit12 K))]
  intro i
  have hXi : MvPolynomial.X i ∈ homogeneousPieces K 1 :=
    MvPolynomial.isHomogeneous_X K i
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)
      (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X i)
        hXi (Nat.zero_lt_one)).inv,
    ← Category.assoc, Proj.basicOpenIsoSpec_inv_ι, structureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact chartRingHom_isStandardSmoothOfRelativeDimension_one_genus_import_recovery_unit12 K i

private def genericPointCandidate_genus_import_recovery_unit12 (K : Type u) [Field K] :
    ProjectiveSpectrum (homogeneousPieces K) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa using (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsPrime)
  not_irrelevant_le := by
    intro h
    have hx : MvPolynomial.X (0 : Fin 2) ∈
        (⊥ : HomogeneousIdeal (homogeneousPieces K)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K)
        Nat.zero_lt_one (X_zero_mem_degree_one K))
    have hx' : MvPolynomial.X (0 : Fin 2) ∈
        (⊥ : Ideal (MvPolynomial (Fin 2) K)) := hx
    exact MvPolynomial.X_ne_zero (R := K) (0 : Fin 2) (Ideal.mem_bot.mp hx')

private lemma irreducibleSpace_projectiveLine_genus_import_recovery_unit12 (K : Type u) [Field K] :
    IrreducibleSpace (scheme K) := by
  rw [irreducibleSpace_def]
  have hclosure : closure ({genericPointCandidate_genus_import_recovery_unit12 K} : Set (scheme K)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change ProjectiveSpectrum (homogeneousPieces K) at x
    change x ∈ closure ({genericPointCandidate_genus_import_recovery_unit12 K} :
      Set (ProjectiveSpectrum (homogeneousPieces K)))
    apply (ProjectiveSpectrum.le_iff_mem_closure (homogeneousPieces K)
      (genericPointCandidate_genus_import_recovery_unit12 K) x).mp
    change (⊥ : HomogeneousIdeal (homogeneousPieces K)) ≤ x.asHomogeneousIdeal
    exact bot_le
  change IsIrreducible (Set.univ : Set (scheme K))
  rw [← hclosure]
  exact isIrreducible_singleton.closure

private lemma isDomain_away_genus_import_recovery_unit12 (K : Type u) [Field K] (i : Fin 2) :
    IsDomain (HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X i)) := by
  letI : IsDomain (homogeneousPieces K 0) :=
    (degreeZeroRingEquiv K).toMulEquiv.isDomain_iff.mp inferInstance
  fin_cases i
  · exact (polynomialAwayZeroAlgEquiv_genus_import_recovery_unit12 K).toRingEquiv.toMulEquiv.isDomain_iff.mp
      (inferInstanceAs (IsDomain (Polynomial (homogeneousPieces K 0))))
  · exact (polynomialAwayAlgEquiv_genus_import_recovery_unit12 K).toRingEquiv.toMulEquiv.isDomain_iff.mp
      (inferInstanceAs (IsDomain (Polynomial (homogeneousPieces K 0))))

private lemma isReduced_projectiveLine_genus_import_recovery_unit12 (K : Type u) [Field K] :
    IsReduced (scheme K) := by
  let U : Fin 2 → (scheme K).Opens := fun i ↦
    Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i)
  have hU : ⨆ i, U i = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero_genus_import_recovery_unit12 K)
  let C : (scheme K).OpenCover := (scheme K).openCoverOfIsOpenCover U hU
  letI (i : C.I₀) : IsReduced (C.X i) := by
    change Fin 2 at i
    change IsReduced (U i)
    have hXi : MvPolynomial.X i ∈ homogeneousPieces K 1 :=
      MvPolynomial.isHomogeneous_X K i
    letI : IsDomain (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X i)) := isDomain_away_genus_import_recovery_unit12 K i
    haveI : IsIntegral
        (Spec (.of (HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X i)))) := inferInstance
    haveI : IsIntegral (U i) := IsIntegral.of_isIso
      (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X i)
        hXi Nat.zero_lt_one).inv
    exact isReduced_of_isIntegral (U i)
  exact IsReduced.of_openCover (scheme K) C

noncomputable instance (K : Type u) [Field K] : IsIntegral (scheme K) := by
  letI : IrreducibleSpace (scheme K) := irreducibleSpace_projectiveLine_genus_import_recovery_unit12 K
  letI : IsReduced (scheme K) := isReduced_projectiveLine_genus_import_recovery_unit12 K
  exact isIntegral_of_irreducibleSpace_of_isReduced (scheme K)

noncomputable instance (K : Type u) [Field K] : IsNoetherian (scheme K) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (structureMap K)
  toCompactSpace := compactSpace_of_universallyClosed (structureMap K)

end
end TauCeti.AlgebraicGeometry.ProjectiveLine

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine affine opens of the existing projective line containing
an arbitrary finite subset over an infinite field. Named downstream consumer:
all finite subsets of the actual order-13 curve lie in an affine open, by its
checked finite hyperelliptic map. The projective-line source and pin are retained
in the complete integration-source manifest.
-/

noncomputable section
open AlgebraicGeometry
namespace MazurTransfer.ProjectiveLineFiniteSubsetAffineOpen
universe u
variable (K : Type u) [Field K]
open TauCeti.AlgebraicGeometry.ProjectiveLine

def linearForm (a : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1

def movingAffineOpen (a : K) : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (linearForm K a)

theorem linearForm_homogeneous (a : K) : linearForm K a ∈ homogeneousPieces K 1 := by
  apply Submodule.sub_mem _ (X_zero_mem_degree_one K)
  simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq] using
    (homogeneousPieces K 1).smul_mem a (X_one_mem_degree_one K)

theorem movingAffineOpen_isAffine (a : K) : IsAffineOpen (movingAffineOpen K a) :=
  Proj.isAffineOpen_basicOpen (homogeneousPieces K) (linearForm K a)
    (linearForm_homogeneous K a) _root_.zero_lt_one

theorem forbiddenParameters_subsingleton (p : scheme K) :
    {a : K | linearForm K a ∈ p.asHomogeneousIdeal.toIdeal}.Subsingleton := by
  intro a ha b hb
  by_contra hab
  let I := p.asHomogeneousIdeal.toIdeal
  have hdiff : MvPolynomial.C (a - b) * MvPolynomial.X (1 : Fin 2) ∈ I := by
    have H := I.sub_mem hb ha
    convert H using 1 <;> simp only [linearForm, map_sub] <;> ring
  have hcunit : IsUnit (MvPolynomial.C (a - b) : MvPolynomial (Fin 2) K) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab)).map MvPolynomial.C
  have hnot : (MvPolynomial.C (a - b) : MvPolynomial (Fin 2) K) ∉ I := by
    intro h
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem I h hcunit)
  have hx1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∈ I :=
    (p.isPrime.mem_or_mem hdiff).resolve_left hnot
  have hx0 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∈ I := by
    have H := I.add_mem ha (I.mul_mem_left (MvPolynomial.C a) hx1)
    simpa only [linearForm, sub_add_cancel] using H
  have hp : p ∈ standardAffineOpen K ⊔ infinityAffineOpen K := by
    rw [standardAffineOpen_sup_infinityAffineOpen_eq_top]
    trivial
  change (MvPolynomial.X (1 : Fin 2) ∉ I) ∨ (MvPolynomial.X (0 : Fin 2) ∉ I) at hp
  exact hp.elim (fun h => h hx1) (fun h => h hx0)

theorem finite_subset_affineOpen [Infinite K] (F : Finset (scheme K)) :
    ∃ U : (scheme K).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical
  have hfinite : {a : K | ∃ p ∈ F, linearForm K a ∈ p.asHomogeneousIdeal.toIdeal}.Finite := by
    have H : (⋃ p ∈ (F : Set (scheme K)),
        {a : K | linearForm K a ∈ p.asHomogeneousIdeal.toIdeal}).Finite :=
      F.finite_toSet.biUnion (fun p _ => (forbiddenParameters_subsingleton K p).finite)
    convert H using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
  obtain ⟨a, ha⟩ := hfinite.exists_notMem
  refine ⟨movingAffineOpen K a, movingAffineOpen_isAffine K a, ?_⟩
  intro p hp
  change linearForm K a ∉ p.asHomogeneousIdeal.toIdeal
  exact fun h => ha ⟨p, hp, h⟩

end MazurTransfer.ProjectiveLineFiniteSubsetAffineOpen
#print axioms MazurTransfer.ProjectiveLineFiniteSubsetAffineOpen.finite_subset_affineOpen

end

end


section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The hyperelliptic map from the order-thirteen curve

This file constructs the degree-two map from the glued order-thirteen curve
to Tau Ceti's actual projective line.  On the ordinary chart it is induced by
`K[x] → K[x,y]/(y²-f(x))`; on the reciprocal chart it is induced by the
coordinate `z = 1/x`.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenHyperellipticMap

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DirectSum
open TauCeti.AlgebraicGeometry

universe u

private lemma zero_lt_one_genus_import_recovery_unit14 : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

section ChartRingMaps

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]

/-- Evaluation of the homogeneous coordinates at `[x:1]`. -/
private def standardCoordinatePolynomialHom_genus_import_recovery_unit14 (x : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 0 then x else 1

private lemma standardCoordinatePolynomialHom_X_one_genus_import_recovery_unit14 (x : A) :
    standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x
        (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [standardCoordinatePolynomialHom_genus_import_recovery_unit14]

/-- The standard projective-line chart ring map sending `X₀/X₁` to
`x`. -/
noncomputable def standardChartRingHom (x : A) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [standardCoordinatePolynomialHom_X_one_genus_import_recovery_unit14]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

@[simp]
theorem standardChartRingHom_affineCoordinateAway (x : A) :
    standardChartRingHom K A x (ProjectiveLine.affineCoordinateAway K) = x := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    ProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [standardCoordinatePolynomialHom_X_one_genus_import_recovery_unit14]; simp) 1
  simpa [standardCoordinatePolynomialHom_genus_import_recovery_unit14] using h

/-- Evaluation of the homogeneous coordinates at `[1:z]`. -/
private def inverseCoordinatePolynomialHom_genus_import_recovery_unit14 (z : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 1 then z else 1

private lemma inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit14 (z : A) :
    inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z
        (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit14]

/-- The infinity projective-line chart ring map sending `X₁/X₀` to
`z`. -/
noncomputable def infinityChartRingHom (z : A) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit14]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

@[simp]
theorem infinityChartRingHom_inverseAffineCoordinateAway (z : A) :
    infinityChartRingHom K A z
        (ProjectiveLine.inverseAffineCoordinateAway K) = z := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    ProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit14]; simp) 1
  simpa [inverseCoordinatePolynomialHom_genus_import_recovery_unit14] using h

private theorem standardCoordinatePolynomialHom_naturality_genus_import_recovery_unit14
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x) =
      standardCoordinatePolynomialHom_genus_import_recovery_unit14 K B (f x) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [standardCoordinatePolynomialHom_genus_import_recovery_unit14]
  · intro i
    fin_cases i <;> simp [standardCoordinatePolynomialHom_genus_import_recovery_unit14]

private theorem infinityCoordinatePolynomialHom_naturality_genus_import_recovery_unit14
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z) =
      inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K B (f z) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit14]
  · intro i
    fin_cases i <;> simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit14]

/-- Homogeneous evaluation is invariant under the projective rescaling
`[x:1] = [1:z]` when `xz=1`. -/
private theorem eval_standard_eq_pow_mul_eval_inverse_genus_import_recovery_unit14
    (p : MvPolynomial (Fin 2) K) (n : ℕ)
    (hp : p.IsHomogeneous n) (x z : A) (hxz : x * z = 1) :
    standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x p =
      x ^ n * inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p := by
  simp only [standardCoordinatePolynomialHom_genus_import_recovery_unit14,
    inverseCoordinatePolynomialHom_genus_import_recovery_unit14, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using h
  simp only [Fin.prod_univ_two,
    if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_neg (by decide : (0 : Fin 2) ≠ 1), if_true, one_pow,
    one_mul, mul_one]
  rw [← hdeg, pow_add]
  calc
    (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 =
        (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 * 1 := by
          rw [mul_one]
    _ = (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 *
        ((x * z) ^ d 1) := by rw [hxz, one_pow]
    _ = (x ^ d 0 * x ^ d 1) *
        ((algebraMap K A) (MvPolynomial.coeff d p) * z ^ d 1) := by
          rw [mul_pow]
          ring

private theorem overlapDenominator_mem_degree_two_genus_import_recovery_unit14 :
    MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) ∈
      ProjectiveLine.homogeneousPieces K 2 := by
  simpa using
    (ProjectiveLine.X_one_mem_degree_one K).mul
      (ProjectiveLine.X_zero_mem_degree_one K)

/-- Evaluation on the common projective-line chart `D₊(X₁X₀)`,
normalized as `[x:1]` with chosen inverse `z`. -/
private noncomputable def overlapChartRingHom_genus_import_recovery_unit14
    (x z : A) (hxz : x * z = 1) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x)
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
      (isUnit_iff_exists_inv.mpr ⟨z, by
        simpa [standardCoordinatePolynomialHom_genus_import_recovery_unit14] using hxz⟩)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)))
      (Localization.Away
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))))

private theorem standardChartRingHom_awayMk_genus_import_recovery_unit14
    (x : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K n) :
    standardChartRingHom K A x
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x p := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x)
    (MvPolynomial.X (1 : Fin 2)) p 1
    (by rw [standardCoordinatePolynomialHom_X_one_genus_import_recovery_unit14]; simp) n
  simpa using h

private theorem infinityChartRingHom_awayMk_genus_import_recovery_unit14
    (z : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K n) :
    infinityChartRingHom K A z
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) n p
          (by simpa using hp)) =
      inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z)
    (MvPolynomial.X (0 : Fin 2)) p 1
    (by rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit14]; simp) n
  simpa using h

private theorem standardChartRingHom_naturality_genus_import_recovery_unit14
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardChartRingHom K A x) =
      standardChartRingHom K B (f x) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    standardChartRingHom_awayMk_genus_import_recovery_unit14 K A x n p hp',
    standardChartRingHom_awayMk_genus_import_recovery_unit14 K B (f x) n p hp']
  exact DFunLike.congr_fun
    (standardCoordinatePolynomialHom_naturality_genus_import_recovery_unit14 K A B f x) p

private theorem infinityChartRingHom_naturality_genus_import_recovery_unit14
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (infinityChartRingHom K A z) =
      infinityChartRingHom K B (f z) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    infinityChartRingHom_awayMk_genus_import_recovery_unit14 K A z n p hp',
    infinityChartRingHom_awayMk_genus_import_recovery_unit14 K B (f z) n p hp']
  exact DFunLike.congr_fun
    (infinityCoordinatePolynomialHom_naturality_genus_import_recovery_unit14 K A B f z) p

private theorem overlapChartRingHom_awayMk_genus_import_recovery_unit14
    (x z : A) (hxz : x * z = 1) (n : ℕ)
    (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K (n • 2)) :
    overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (overlapDenominator_mem_degree_two_genus_import_recovery_unit14 K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x p * z ^ n := by
  simp only [overlapChartRingHom_genus_import_recovery_unit14, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x)
    (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
    p z (by simpa [standardCoordinatePolynomialHom_genus_import_recovery_unit14] using hxz) n
  simpa using h

private theorem overlapChartRingHom_comp_standardAwayMap_genus_import_recovery_unit14
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) rfl) =
      standardChartRingHom K A x := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk_genus_import_recovery_unit14 K A x z hxz n
      (p * MvPolynomial.X (0 : Fin 2) ^ n),
    standardChartRingHom_awayMk_genus_import_recovery_unit14 K A x n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom_genus_import_recovery_unit14,
      MvPolynomial.eval₂Hom_X']
    simp only [if_pos]
    rw [mul_assoc, ← mul_pow, hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (ProjectiveLine.X_zero_mem_degree_one K))

private theorem overlapChartRingHom_comp_infinityAwayMap_genus_import_recovery_unit14
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K)
          (mul_comm _ _)) =
      infinityChartRingHom K A z := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk_genus_import_recovery_unit14 K A x z hxz n
      (p * MvPolynomial.X (1 : Fin 2) ^ n),
    infinityChartRingHom_awayMk_genus_import_recovery_unit14 K A z n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom_genus_import_recovery_unit14,
      MvPolynomial.eval₂Hom_X']
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), one_pow,
      mul_one]
    change standardCoordinatePolynomialHom_genus_import_recovery_unit14 K A x p * z ^ n =
      inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p
    rw [eval_standard_eq_pow_mul_eval_inverse_genus_import_recovery_unit14 K A p n hp' x z hxz]
    calc
      (x ^ n * inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p) * z ^ n =
          inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p * (x * z) ^ n := by
            rw [mul_pow]
            ring
      _ = inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K A z p := by
        rw [hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (ProjectiveLine.X_one_mem_degree_one K))

end ChartRingMaps

section ChartFiniteness

variable (K : Type u) [Field K]

private noncomputable def standardPolynomialToAway_genus_import_recovery_unit14 :
    Polynomial K →+*
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (ProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)))).comp
      (ProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (ProjectiveLine.affineCoordinateAway K)

private theorem standardChartRingHom_comp_standardPolynomialToAway_genus_import_recovery_unit14 :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).comp
        (standardPolynomialToAway_genus_import_recovery_unit14 K) =
      (AdjoinRoot.of
        (XOneThirteenAffineCurve.affineEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show standardPolynomialToAway_genus_import_recovery_unit14 K (Polynomial.C k) =
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        ProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((ProjectiveLine.degreeZeroRingEquiv K k :
            ProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [ProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      standardChartRingHom_awayMk_genus_import_recovery_unit14 K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show standardCoordinatePolynomialHom_genus_import_recovery_unit14 K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) (MvPolynomial.C k) =
      algebraMap K (XOneThirteenAffineCurve.CoordinateRing K) k by
        simp [standardCoordinatePolynomialHom_genus_import_recovery_unit14]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenAffineCurve.CoordinateRing K) k)
  · simp [standardPolynomialToAway_genus_import_recovery_unit14,
      XOneThirteenAffineCurve.xCoordinate]

private theorem affineEquation_monic_genus_import_recovery_unit14 :
    (XOneThirteenAffineCurve.affineEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The standard chart of the hyperelliptic map is finite. -/
theorem standardChartRingHom_finite :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := standardPolynomialToAway_genus_import_recovery_unit14 K)
  rw [standardChartRingHom_comp_standardPolynomialToAway_genus_import_recovery_unit14 K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot (XOneThirteenAffineCurve.affineEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (affineEquation_monic_genus_import_recovery_unit14 K |>.finite_adjoinRoot)

private noncomputable def infinityPolynomialToAway_genus_import_recovery_unit14 :
    Polynomial K →+*
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (ProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2)))).comp
      (ProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (ProjectiveLine.inverseAffineCoordinateAway K)

private theorem infinityChartRingHom_comp_infinityPolynomialToAway_genus_import_recovery_unit14 :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).comp
        (infinityPolynomialToAway_genus_import_recovery_unit14 K) =
      (AdjoinRoot.of
        (XOneThirteenProjectiveCurve.reciprocalEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show infinityPolynomialToAway_genus_import_recovery_unit14 K (Polynomial.C k) =
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        ProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((ProjectiveLine.degreeZeroRingEquiv K k :
            ProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [ProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      infinityChartRingHom_awayMk_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K)
        (MvPolynomial.C k) =
      algebraMap K (XOneThirteenProjectiveCurve.ReciprocalRing K) k by
        simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit14]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenProjectiveCurve.ReciprocalRing K) k)
  · simp [infinityPolynomialToAway_genus_import_recovery_unit14,
      XOneThirteenProjectiveCurve.zCoordinate]

private theorem reciprocalEquation_monic_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.reciprocalEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The infinity chart of the hyperelliptic map is finite. -/
theorem infinityChartRingHom_finite :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := infinityPolynomialToAway_genus_import_recovery_unit14 K)
  rw [infinityChartRingHom_comp_infinityPolynomialToAway_genus_import_recovery_unit14 K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot
      (XOneThirteenProjectiveCurve.reciprocalEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (reciprocalEquation_monic_genus_import_recovery_unit14 K |>.finite_adjoinRoot)

end ChartFiniteness

section ChartMorphisms

variable (K : Type u) [Field K]

private theorem projectiveLine_chart_maps_eq_genus_import_recovery_unit14
    (A : Type u) [CommRing A] [Algebra K A]
    (x z : A) (hxz : x * z = 1) :
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14 =
      Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14 := by
  let H := ProjectiveLine.homogeneousPieces K
  let X₀ : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let X₁ : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let q : MvPolynomial (Fin 2) K := X₁ * X₀
  let hq : q ∈ H 2 := overlapDenominator_mem_degree_two_genus_import_recovery_unit14 K
  have hstd := overlapChartRingHom_comp_standardAwayMap_genus_import_recovery_unit14 K A x z hxz
  have hinf := overlapChartRingHom_comp_infinityAwayMap_genus_import_recovery_unit14 K A x z hxz
  calc
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
          Proj.awayι H X₁ (ProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one_genus_import_recovery_unit14 =
        (Spec.map (CommRingCat.ofHom (overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₁) (x := q)
              (ProjectiveLine.X_zero_mem_degree_one K) rfl))) ≫
          Proj.awayι H X₁ (ProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one_genus_import_recovery_unit14 := by
              rw [← Spec.map_comp]
              congr 2
              apply CommRingCat.hom_ext
              exact hstd.symm
    _ = Spec.map (CommRingCat.ofHom
          (overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz)) ≫
        Proj.awayι H q hq (by omega) := by
          rw [Category.assoc,
            Proj.SpecMap_awayMap_awayι
              (f := X₁) (g := X₀) (x := q) H
              (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
              (ProjectiveLine.X_zero_mem_degree_one K) rfl]
    _ = (Spec.map (CommRingCat.ofHom
          (overlapChartRingHom_genus_import_recovery_unit14 K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₀) (x := q)
              (ProjectiveLine.X_one_mem_degree_one K)
              (mul_comm X₁ X₀)))) ≫
        Proj.awayι H X₀ (ProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one_genus_import_recovery_unit14 := by
            rw [Category.assoc,
              Proj.SpecMap_awayMap_awayι
                (f := X₀) (g := X₁) (x := q) H
                (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
                (ProjectiveLine.X_one_mem_degree_one K) (mul_comm X₁ X₀)]
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι H X₀ (ProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one_genus_import_recovery_unit14 := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hinf

/-- The ordinary hyperelliptic chart map, with projective coordinate
`[x:1]`. -/
noncomputable def ordinaryChartToProjectiveLine :
    XOneThirteenAffineCurve.scheme K ⟶ ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
    Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14

/-- The reciprocal hyperelliptic chart map, with projective coordinate
`[1:z]`. -/
noncomputable def reciprocalChartToProjectiveLine :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
    Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14

private theorem ordinaryChartToProjectiveLine_toSpecZero_genus_import_recovery_unit14 :
    ordinaryChartToProjectiveLine K ≫
        Proj.toSpecZero (ProjectiveLine.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K (XOneThirteenAffineCurve.CoordinateRing K)).comp
          (ProjectiveLine.degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ordinaryChartToProjectiveLine, Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (ProjectiveLine.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (ProjectiveLine.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2)))
        (ProjectiveLine.degreeZeroRingEquiv K r)) =
    algebraMap K (XOneThirteenAffineCurve.CoordinateRing K) r
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom_genus_import_recovery_unit14 K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K))
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [standardCoordinatePolynomialHom_X_one_genus_import_recovery_unit14]; simp) 0
  convert h using 1
  · congr 1
  · simp [standardCoordinatePolynomialHom_genus_import_recovery_unit14]

private theorem reciprocalChartToProjectiveLine_toSpecZero_genus_import_recovery_unit14 :
    reciprocalChartToProjectiveLine K ≫
        Proj.toSpecZero (ProjectiveLine.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K
            (XOneThirteenProjectiveCurve.ReciprocalRing K)).comp
          (ProjectiveLine.degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [reciprocalChartToProjectiveLine, Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (ProjectiveLine.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (ProjectiveLine.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))
        (ProjectiveLine.degreeZeroRingEquiv K r)) =
    algebraMap K (XOneThirteenProjectiveCurve.ReciprocalRing K) r
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom_genus_import_recovery_unit14 K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K))
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero_genus_import_recovery_unit14]; simp) 0
  convert h using 1
  · congr 1
  · simp [inverseCoordinatePolynomialHom_genus_import_recovery_unit14]

@[simp, reassoc]
theorem ordinaryChartToProjectiveLine_structureMap :
    ordinaryChartToProjectiveLine K ≫ ProjectiveLine.structureMap K =
      XOneThirteenProjectiveCurve.ordinaryChartToBase K := by
  rw [ProjectiveLine.structureMap, ← Category.assoc,
    ordinaryChartToProjectiveLine_toSpecZero_genus_import_recovery_unit14, ← Spec.map_comp]
  unfold XOneThirteenProjectiveCurve.ordinaryChartToBase
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[simp, reassoc]
theorem reciprocalChartToProjectiveLine_structureMap :
    reciprocalChartToProjectiveLine K ≫ ProjectiveLine.structureMap K =
      XOneThirteenProjectiveCurve.reciprocalChartToBase K := by
  rw [ProjectiveLine.structureMap, ← Category.assoc,
    reciprocalChartToProjectiveLine_toSpecZero_genus_import_recovery_unit14, ← Spec.map_comp]
  unfold XOneThirteenProjectiveCurve.reciprocalChartToBase
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

theorem ordinaryChartToProjectiveLine_preimage_standardAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K = ⊤ := by
  rw [show ProjectiveLine.standardAffineOpen K =
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).opensRange by
    exact (Proj.opensRange_awayι _ _
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).symm]
  unfold ordinaryChartToProjectiveLine XOneThirteenAffineCurve.scheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem inverseAffineCoordinateAway_eq_isLocalizationElem_genus_import_recovery_unit14 :
    ProjectiveLine.inverseAffineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveLine.X_zero_mem_degree_one K)
        (ProjectiveLine.X_one_mem_degree_one K) := by
  simp [ProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  unfold reciprocalChartToProjectiveLine
    XOneThirteenProjectiveCurve.reciprocalScheme
  change (Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
      Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14) ⁻¹ᵁ
      Proj.basicOpen (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (ProjectiveLine.homogeneousPieces K)
    (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
    (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← inverseAffineCoordinateAway_eq_isLocalizationElem_genus_import_recovery_unit14 K]
  exact infinityChartRingHom_inverseAffineCoordinateAway K
    (XOneThirteenProjectiveCurve.ReciprocalRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

theorem reciprocalChartToProjectiveLine_preimage_infinityAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K = ⊤ := by
  rw [show ProjectiveLine.infinityAffineOpen K =
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).opensRange by
    exact (Proj.opensRange_awayι _ _
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).symm]
  unfold reciprocalChartToProjectiveLine
    XOneThirteenProjectiveCurve.reciprocalScheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem affineCoordinateAway_eq_isLocalizationElem_genus_import_recovery_unit14 :
    ProjectiveLine.affineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveLine.X_one_mem_degree_one K)
        (ProjectiveLine.X_zero_mem_degree_one K) := by
  simp [ProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenAffineCurve.xCoordinate K) := by
  unfold ordinaryChartToProjectiveLine
  change (Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
      Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14) ⁻¹ᵁ
      Proj.basicOpen (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (ProjectiveLine.homogeneousPieces K)
    (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
    (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← affineCoordinateAway_eq_isLocalizationElem_genus_import_recovery_unit14 K]
  exact standardChartRingHom_affineCoordinateAway K
    (XOneThirteenAffineCurve.CoordinateRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private theorem ordinary_ne_reciprocal_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private theorem ordinaryReciprocalOverlapInclusion_eq_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K))) := by
  rfl

private theorem reciprocalOrdinaryOverlapInclusion_eq_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenProjectiveCurve.ReciprocalRing K)
          (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K))) := by
  rfl

private theorem ordinaryReciprocalOverlapTransition_eq_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom := by
  rfl

private theorem reciprocalOrdinaryOverlapTransition_eq_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary_genus_import_recovery_unit14) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq_genus_import_recovery_unit14]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary_genus_import_recovery_unit14).opensRange =
        reciprocalOverlapOpen_genus_import_recovery_unit14 K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen_genus_import_recovery_unit14 :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      reciprocalOverlapOpen_genus_import_recovery_unit14 K := by
  exact reciprocalChartToProjectiveLine_preimage_standardAffineOpen K

private theorem reciprocalGlueOverlap_opensRange_genus_import_recovery_unit14 :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen_genus_import_recovery_unit14 K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal_genus_import_recovery_unit14, reciprocal_ne_ordinary_genus_import_recovery_unit14]
  simp only [dif_neg reciprocal_ne_ordinary_genus_import_recovery_unit14]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange_genus_import_recovery_unit14 K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 :
    reciprocalOverlapOpen_genus_import_recovery_unit14 K =
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange_genus_import_recovery_unit14 K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange_genus_import_recovery_unit14 K).symm

/-- On the reciprocal chart, the overlap with the ordinary chart is exactly
the principal open where the reciprocal coordinate `z` is nonzero. -/
@[simp]
theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 K).symm

private instance ordinaryOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        ordinary_ne_reciprocal_genus_import_recovery_unit14) := by
  rw [ordinaryReciprocalOverlapInclusion_eq_genus_import_recovery_unit14]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenAffineCurve.xCoordinate K)

private noncomputable abbrev ordinaryOverlapOpen_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenAffineCurve.xCoordinate K)

private theorem ordinaryOverlapInclusion_opensRange_genus_import_recovery_unit14 :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      ordinary_ne_reciprocal_genus_import_recovery_unit14).opensRange =
        ordinaryOverlapOpen_genus_import_recovery_unit14 K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private instance ordinaryGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen_genus_import_recovery_unit14 :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      ordinaryOverlapOpen_genus_import_recovery_unit14 K := by
  exact ordinaryChartToProjectiveLine_preimage_infinityAffineOpen K

private theorem ordinaryGlueOverlap_opensRange_genus_import_recovery_unit14 :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      ordinaryOverlapOpen_genus_import_recovery_unit14 K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal_genus_import_recovery_unit14, reciprocal_ne_ordinary_genus_import_recovery_unit14]
  simp only [dif_neg ordinary_ne_reciprocal_genus_import_recovery_unit14]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ordinaryOverlapInclusion_opensRange_genus_import_recovery_unit14 K

private theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.ordinaryChartMap K q ∈
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem ordinaryOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 :
    ordinaryOverlapOpen_genus_import_recovery_unit14 K =
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange :=
  (ordinaryGlueOverlap_opensRange_genus_import_recovery_unit14 K).symm.trans
    (ordinaryChartMap_preimage_reciprocalChartMap_opensRange_genus_import_recovery_unit14 K).symm

/-- On the ordinary chart, the overlap with the reciprocal chart is exactly
the principal open where `x` is nonzero. -/
@[simp]
theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenAffineCurve.xCoordinate K) := by
  exact (ordinaryOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 K).symm

private theorem ordinary_reciprocal_hyperelliptic_compatible_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        ordinaryChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
        reciprocalChartToProjectiveLine K := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let B := XOneThirteenProjectiveCurve.ReciprocalRing K
  let LA := XOneThirteenProjectiveCurve.OrdinaryOverlapRing K
  let LB := XOneThirteenProjectiveCurve.ReciprocalOverlapRing K
  let x : LA := algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)
  let z : LA := IsLocalization.Away.invSelf
    (XOneThirteenAffineCurve.xCoordinate K)
  let ordinaryLocalization : A →ₐ[K] LA :=
    IsScalarTower.toAlgHom K A LA
  let reciprocalToOrdinary : B →ₐ[K] LA :=
    (XOneThirteenProjectiveCurve.reciprocalToOrdinary K).comp
      (IsScalarTower.toAlgHom K B LB)
  have hxz : x * z = 1 := by
    exact IsLocalization.Away.mul_invSelf
      (XOneThirteenAffineCurve.xCoordinate K)
  have hz : reciprocalToOrdinary
      (XOneThirteenProjectiveCurve.zCoordinate K) = z := by
    change XOneThirteenProjectiveCurve.reciprocalToOrdinary K
      (algebraMap B LB (XOneThirteenProjectiveCurve.zCoordinate K)) = z
    rw [XOneThirteenProjectiveCurve.reciprocalToOrdinary_algebraMap,
      XOneThirteenProjectiveCurve.reciprocalToOrdinaryBase_z]
    rfl
  have hordinary := standardChartRingHom_naturality_genus_import_recovery_unit14 K A LA
    ordinaryLocalization (XOneThirteenAffineCurve.xCoordinate K)
  have hreciprocal := infinityChartRingHom_naturality_genus_import_recovery_unit14 K B LA
    reciprocalToOrdinary (XOneThirteenProjectiveCurve.zCoordinate K)
  rw [hz] at hreciprocal
  calc
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        ordinaryChartToProjectiveLine K =
      Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14 := by
      rw [ordinaryReciprocalOverlapInclusion_eq_genus_import_recovery_unit14]
      unfold ordinaryChartToProjectiveLine XOneThirteenAffineCurve.scheme
      change Spec.map (CommRingCat.ofHom (algebraMap A LA)) ≫
          (Spec.map (CommRingCat.ofHom
            (standardChartRingHom K A
              (XOneThirteenAffineCurve.xCoordinate K))) ≫
            Proj.awayι (ProjectiveLine.homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2))
              (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14) =
        Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
          Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hordinary
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14 :=
      projectiveLine_chart_maps_eq_genus_import_recovery_unit14 K LA x z hxz
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
        reciprocalChartToProjectiveLine K := by
      rw [ordinaryReciprocalOverlapTransition_eq_genus_import_recovery_unit14,
        XOneThirteenProjectiveCurve.overlapSchemeIso_hom,
        reciprocalOrdinaryOverlapInclusion_eq_genus_import_recovery_unit14]
      unfold reciprocalChartToProjectiveLine
        XOneThirteenProjectiveCurve.reciprocalScheme
      change Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
          Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14 =
        Spec.map (CommRingCat.ofHom
          (XOneThirteenProjectiveCurve.reciprocalToOrdinary K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B LB)) ≫
          (Spec.map (CommRingCat.ofHom
            (infinityChartRingHom K B
              (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
            Proj.awayι (ProjectiveLine.homogeneousPieces K)
              (MvPolynomial.X (0 : Fin 2))
              (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14)
      symm
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hreciprocal

private theorem reciprocal_ordinary_hyperelliptic_compatible_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
        reciprocalChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        ordinaryChartToProjectiveLine K := by
  let l := XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
    reciprocalChartToProjectiveLine K
  calc
    l = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom ≫ l := by
      rw [(XOneThirteenProjectiveCurve.overlapSchemeIso K).inv_hom_id_assoc]
    _ = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        ordinaryChartToProjectiveLine K := by
      rw [ordinary_reciprocal_hyperelliptic_compatible_genus_import_recovery_unit14 K]
      rfl
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary_genus_import_recovery_unit14 ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal_genus_import_recovery_unit14 ≫
        ordinaryChartToProjectiveLine K := by
      rw [reciprocalOrdinaryOverlapTransition_eq_genus_import_recovery_unit14]

/-- The chartwise hyperelliptic maps before descent through the gluing. -/
noncomputable def chartToProjectiveLine :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      XOneThirteenProjectiveCurve.chartScheme K i ⟶
        ProjectiveLine.scheme K
  | .ordinary => ordinaryChartToProjectiveLine K
  | .reciprocal => reciprocalChartToProjectiveLine K

/-- The hyperelliptic map descended from the two checked chart maps. -/
noncomputable def gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.curveScheme K ⟶
      ProjectiveLine.scheme K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  exact Limits.Multicoequalizer.desc
    (XOneThirteenProjectiveCurve.glueData K).toGlueData.diagram
    (ProjectiveLine.scheme K) (chartToProjectiveLine K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal_genus_import_recovery_unit14, reciprocal_ne_ordinary_genus_import_recovery_unit14,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal_genus_import_recovery_unit14,
          dif_neg reciprocal_ne_ordinary_genus_import_recovery_unit14, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact ordinary_reciprocal_hyperelliptic_compatible_genus_import_recovery_unit14 K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal_genus_import_recovery_unit14, reciprocal_ne_ordinary_genus_import_recovery_unit14,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal_genus_import_recovery_unit14,
          dif_neg reciprocal_ne_ordinary_genus_import_recovery_unit14, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact reciprocal_ordinary_hyperelliptic_compatible_genus_import_recovery_unit14 K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
        gluedHyperellipticMap K =
      ordinaryChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.ordinaryChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
        gluedHyperellipticMap K =
      reciprocalChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.reciprocalChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

theorem gluedHyperellipticMap_preimage_standardAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ⊤ := ordinaryChartToProjectiveLine_preimage_standardAffineOpen K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = reciprocalOverlapOpen_genus_import_recovery_unit14 K :=
        reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen_genus_import_recovery_unit14 K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
        reciprocalOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 K
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

theorem gluedHyperellipticMap_preimage_infinityAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ordinaryOverlapOpen_genus_import_recovery_unit14 K :=
        ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen_genus_import_recovery_unit14 K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange :=
        ordinaryOverlapOpen_eq_chartMap_preimage_genus_import_recovery_unit14 K
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = ⊤ := reciprocalChartToProjectiveLine_preimage_infinityAffineOpen K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

private noncomputable abbrev projectiveLineChartScheme_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.Chart.{u} → Scheme
  | .ordinary => Spec (.of <|
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
  | .reciprocal => Spec (.of <|
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))

private noncomputable def projectiveLineChartMap_genus_import_recovery_unit14 :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      projectiveLineChartScheme_genus_import_recovery_unit14 K i ⟶ ProjectiveLine.scheme K
  | .ordinary => Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14
  | .reciprocal => Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14

private instance projectiveLineChartMap_isOpenImmersion
    (i : XOneThirteenProjectiveCurve.Chart.{u}) :
    IsOpenImmersion (projectiveLineChartMap_genus_import_recovery_unit14 K i) := by
  rcases i with (_ | _)
  · change IsOpenImmersion
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14)
    infer_instance
  · change IsOpenImmersion
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14)
    infer_instance

private theorem projectiveLineChartMap_ordinary_opensRange_genus_import_recovery_unit14 :
    (projectiveLineChartMap_genus_import_recovery_unit14 K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      ProjectiveLine.standardAffineOpen K := by
  exact Proj.opensRange_awayι (ProjectiveLine.homogeneousPieces K)
    (MvPolynomial.X (1 : Fin 2))
    (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14

private theorem projectiveLineChartMap_reciprocal_opensRange_genus_import_recovery_unit14 :
    (projectiveLineChartMap_genus_import_recovery_unit14 K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      ProjectiveLine.infinityAffineOpen K := by
  exact Proj.opensRange_awayι (ProjectiveLine.homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2))
    (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14

private noncomputable def projectiveLineChartCover_genus_import_recovery_unit14 :
    (ProjectiveLine.scheme K).OpenCover where
  I₀ := XOneThirteenProjectiveCurve.Chart.{u}
  X := projectiveLineChartScheme_genus_import_recovery_unit14 K
  f := projectiveLineChartMap_genus_import_recovery_unit14 K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp : p ∈ ProjectiveLine.standardAffineOpen K ⊔
          ProjectiveLine.infinityAffineOpen K := by
        rw [ProjectiveLine.standardAffineOpen_sup_infinityAffineOpen_eq_top]
        trivial
      change p ∈ (ProjectiveLine.standardAffineOpen K :
          Set (ProjectiveLine.scheme K)) ∪
        (ProjectiveLine.infinityAffineOpen K :
          Set (ProjectiveLine.scheme K)) at hp
      rcases hp with hp | hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.ordinary, ?_⟩
        change p ∈ (Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.reciprocal, ?_⟩
        change p ∈ (Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one_genus_import_recovery_unit14).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
    · intro i
      exact projectiveLineChartMap_isOpenImmersion K i

private noncomputable def ordinaryChartFiniteMap_genus_import_recovery_unit14 :
    XOneThirteenAffineCurve.scheme K ⟶
      projectiveLineChartScheme_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)))

private noncomputable def reciprocalChartFiniteMap_genus_import_recovery_unit14 :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      projectiveLineChartScheme_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)))

private theorem ordinaryChartSquare_isPullback_genus_import_recovery_unit14 :
    IsPullback (ordinaryChartFiniteMap_genus_import_recovery_unit14 K)
      (XOneThirteenProjectiveCurve.ordinaryChartMap K)
      (projectiveLineChartMap_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [ordinaryChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_ordinary_opensRange_genus_import_recovery_unit14]
    exact gluedHyperellipticMap_preimage_standardAffineOpen K

private theorem reciprocalChartSquare_isPullback_genus_import_recovery_unit14 :
    IsPullback (reciprocalChartFiniteMap_genus_import_recovery_unit14 K)
      (XOneThirteenProjectiveCurve.reciprocalChartMap K)
      (projectiveLineChartMap_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap_genus_import_recovery_unit14 K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [reciprocalChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_reciprocal_opensRange_genus_import_recovery_unit14]
    exact gluedHyperellipticMap_preimage_infinityAffineOpen K

/-- The morphism property underlying `IsFinite`, named explicitly so that
Mathlib's affine-local framework can elaborate it at the default transparency
setting. -/
private abbrev finiteMorphismProperty_genus_import_recovery_unit14 : MorphismProperty Scheme :=
  fun {_ _} f => IsFinite f

private instance finiteMorphismProperty_hasAffineProperty :
    HasAffineProperty finiteMorphismProperty_genus_import_recovery_unit14 (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away
    RingHom.finite_ofLocalizationSpan]
  simp [finiteMorphismProperty_genus_import_recovery_unit14, isFinite_iff]

private theorem ordinaryCoverPullbackHom_isFinite_genus_import_recovery_unit14 :
    IsFinite ((projectiveLineChartCover_genus_import_recovery_unit14 K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := ordinaryChartSquare_isPullback_genus_import_recovery_unit14 K
  change finiteMorphismProperty_genus_import_recovery_unit14 (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap_genus_import_recovery_unit14 K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty_genus_import_recovery_unit14) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact standardChartRingHom_finite K

private theorem reciprocalCoverPullbackHom_isFinite_genus_import_recovery_unit14 :
    IsFinite ((projectiveLineChartCover_genus_import_recovery_unit14 K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := reciprocalChartSquare_isPullback_genus_import_recovery_unit14 K
  change finiteMorphismProperty_genus_import_recovery_unit14 (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap_genus_import_recovery_unit14 K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty_genus_import_recovery_unit14) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact infinityChartRingHom_finite K

noncomputable instance gluedHyperellipticMap_isFinite :
    IsFinite (gluedHyperellipticMap K) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (P := finiteMorphismProperty_genus_import_recovery_unit14) (projectiveLineChartCover_genus_import_recovery_unit14 K)
  intro i
  rcases i with (_ | _)
  · exact ordinaryCoverPullbackHom_isFinite_genus_import_recovery_unit14 K
  · exact reciprocalCoverPullbackHom_isFinite_genus_import_recovery_unit14 K

end ChartMorphisms

end MazurTorsion.XOneThirteenHyperellipticMap

namespace MazurTorsion.XOneThirteenProjectiveCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

variable (K : Type u) [Field K]

/-- The degree-two coordinate map from the glued order-thirteen curve to
Tau Ceti's concrete projective line. -/
noncomputable def hyperellipticMap :
    curveScheme K ⟶ ProjectiveLine.scheme K :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap K

@[simp, reassoc]
theorem ordinaryChartMap_hyperellipticMap :
    ordinaryChartMap K ≫ hyperellipticMap K =
      XOneThirteenHyperellipticMap.ordinaryChartToProjectiveLine K := by
  exact XOneThirteenHyperellipticMap.ordinaryChartMap_gluedHyperellipticMap K

@[simp, reassoc]
theorem reciprocalChartMap_hyperellipticMap :
    reciprocalChartMap K ≫ hyperellipticMap K =
      XOneThirteenHyperellipticMap.reciprocalChartToProjectiveLine K := by
  exact XOneThirteenHyperellipticMap.reciprocalChartMap_gluedHyperellipticMap K

@[simp]
theorem hyperellipticMap_preimage_standardAffineOpen :
    hyperellipticMap K ⁻¹ᵁ ProjectiveLine.standardAffineOpen K =
      (ordinaryChartMap K).opensRange :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_preimage_standardAffineOpen K

@[simp]
theorem hyperellipticMap_preimage_infinityAffineOpen :
    hyperellipticMap K ⁻¹ᵁ ProjectiveLine.infinityAffineOpen K =
      (reciprocalChartMap K).opensRange :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_preimage_infinityAffineOpen K

noncomputable instance hyperellipticMap_isFinite :
    IsFinite (hyperellipticMap K) :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_isFinite K

/-- The structure morphism obtained by gluing the affine algebra maps is the
finite hyperelliptic map followed by the structure morphism of projective
line. -/
theorem curveToBase_eq_hyperellipticMap_comp_structureMap :
    curveToBase K =
      hyperellipticMap K ≫ ProjectiveLine.structureMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  apply Limits.Multicoequalizer.hom_ext
  intro i
  rcases i with (_ | _)
  · change ordinaryChartMap K ≫ curveToBase K =
      ordinaryChartMap K ≫ hyperellipticMap K ≫
        ProjectiveLine.structureMap K
    rw [ordinaryChartMap_curveToBase,
      ordinaryChartMap_hyperellipticMap_assoc,
      XOneThirteenHyperellipticMap.ordinaryChartToProjectiveLine_structureMap]
  · change reciprocalChartMap K ≫ curveToBase K =
      reciprocalChartMap K ≫ hyperellipticMap K ≫
        ProjectiveLine.structureMap K
    rw [reciprocalChartMap_curveToBase,
      reciprocalChartMap_hyperellipticMap_assoc,
      XOneThirteenHyperellipticMap.reciprocalChartToProjectiveLine_structureMap]

/-- The actual glued order-thirteen curve is proper over its coefficient
field.  This is the first downstream consumer of the structural-morphism
comparison above. -/
noncomputable instance curveToBase_isProper : IsProper (curveToBase K) := by
  rw [curveToBase_eq_hyperellipticMap_comp_structureMap]
  infer_instance

/-- The actual glued order-thirteen curve is Noetherian.  Local
Noetherianity descends along the finite hyperelliptic map, while compactness
comes from the proper structure morphism. -/
noncomputable instance curveScheme_isNoetherian : IsNoetherian (curveScheme K) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (hyperellipticMap K)
  toCompactSpace := compactSpace_of_universallyClosed (curveToBase K)

end MazurTorsion.XOneThirteenProjectiveCurve

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: any finite subset of the unchanged explicit order-13 curve
lies in an actual affine open, by the checked finite hyperelliptic map. Named
downstream consumer: the finset_subset_affineOpen field of its genuine official
FLT CurveModel. No abstract curve or missing affine-open axiom is substituted.
-/

noncomputable section
open AlgebraicGeometry
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Infinite K]

theorem actual_curve_finite_subset_affineOpen (F : Finset (curveScheme K)) :
    ∃ U : (curveScheme K).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨U, hU, hF⟩ :=
    MazurTransfer.ProjectiveLineFiniteSubsetAffineOpen.finite_subset_affineOpen K
      (F.image (hyperellipticMap K))
  refine ⟨hyperellipticMap K ⁻¹ᵁ U, hU.preimage (hyperellipticMap K), ?_⟩
  intro x hx
  exact hF _ (Finset.mem_image_of_mem (hyperellipticMap K) hx)

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_curve_finite_subset_affineOpen

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: a genuine complete official FLT CurveModel whose scheme is
literally the unchanged explicit order-13 curve and whose function-field
identification is the identity. Named downstream consumer: the official FLT
unit-sheaf Cech H1 versus genusFF comparison. Every place and affine-open field
is proved using the actual curve; no CurveModel existence hypothesis is added.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) := curveScheme_isIntegral K

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) :=
  curveToBase_smooth_relativeDimension_one K

abbrev actualCurveFunctionField : Type u := (curveScheme K).functionField

instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

def actualPlaceOfPoint (x : closedPoints (curveScheme K)) : Place K (actualCurveFunctionField K) :=
  Classical.choose (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_stalk_range (x : closedPoints (curveScheme K)) :
    (algebraMap ((curveScheme K).presheaf.stalk x.1) (actualCurveFunctionField K)).range =
      (actualPlaceOfPoint K x).toValuationSubring.toSubring :=
  Classical.choose_spec (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_bijective : Function.Bijective (actualPlaceOfPoint K) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact _root_.AlgebraicCurve.eq_of_range_stalk_eq (curveToBase K) x.1 y.1
      (by rw [actualPlaceOfPoint_stalk_range, actualPlaceOfPoint_stalk_range, hxy])
  · intro v
    obtain ⟨x, hx, hrange⟩ :=
      _root_.AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase K) v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]

def actualCurveModel : CurveModel K (actualCurveFunctionField K) where
  C := curveScheme K
  toBase := curveToBase K
  isIntegral := actualCurve_isIntegral K
  isProper := curveToBase_isProper K
  smooth := curveToBase_smooth_relativeDimension_one K
  ffEquiv := RingEquiv.refl _
  ffEquiv_algebraMap := fun _ => rfl
  placeOfPoint := actualPlaceOfPoint K
  placeOfPoint_bijective := actualPlaceOfPoint_bijective K
  range_stalk_eq := fun x => by
    rw [← actualPlaceOfPoint_stalk_range K x]
    ext f
    simp
  finset_subset_affineOpen := actual_curve_finite_subset_affineOpen K

theorem actualCurveModel_C : (actualCurveModel K).C = curveScheme K := rfl

theorem actualCurveModel_toBase : (actualCurveModel K).toBase = curveToBase K := rfl

def actualCurveModelIso : (actualCurveModel K).C ≅ curveScheme K := Iso.refl _

theorem actualCurveModelIso_over_base :
    (actualCurveModelIso K).hom ≫ curveToBase K = (actualCurveModel K).toBase := by
  exact Category.id_comp _

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualPlaceOfPoint_bijective
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualCurveModel
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualCurveModelIso_over_base

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the full genuine FLT function-field curve structure on the
original order-13 scheme's generic stalk. Named downstream consumer: actual
Riemann–Roch existence and global cohomology/genus. Principal divisors, finite
place residue fields and rank-one Kähler differentials are proved together;
the IsCurveOver class is not assumed.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

instance actualFunctionFieldIsCurveOver : IsCurveOver K (actualCurveFunctionField K) :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (curveToBase K) (RingEquiv.refl _) (fun _ => rfl)

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualFunctionFieldIsCurveOver

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the genuine two-affine-open cover of the unchanged glued
order-thirteen curve. Named downstream consumer: the actual structure-sheaf
section comparison with the complete official FLT Cech interface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K]

def ordinaryOpen : (curveScheme K).Opens := (ordinaryChartMap K).opensRange
def reciprocalOpen : (curveScheme K).Opens := (reciprocalChartMap K).opensRange

theorem chart_opens_sup_eq_top : ordinaryOpen K ⊔ reciprocalOpen K = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ Set.range (ordinaryChartMap K) ∨ x ∈ Set.range (reciprocalChartMap K)
  obtain ⟨i, y, hy⟩ := (glueData K).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem curveScheme_isSeparated : (curveScheme K).IsSeparated := by
  have h : IsSeparated (curveToBase K ≫ terminal.from (Spec (.of K))) := inferInstance
  refine ⟨?_⟩
  simpa only [terminal.comp_from] using h

def actualTwoAffineOpenCover : (curveScheme K).TwoAffineOpenCover := by
  haveI := curveScheme_isSeparated K
  exact {
    U0 := ordinaryOpen K
    U1 := reciprocalOpen K
    isAffineOpen_U0 := isAffineOpen_opensRange (ordinaryChartMap K)
    isAffineOpen_U1 := isAffineOpen_opensRange (reciprocalChartMap K)
    sup_eq_top := chart_opens_sup_eq_top K
    isAffineOpen_inf := (isAffineOpen_opensRange (ordinaryChartMap K)).inf
      (isAffineOpen_opensRange (reciprocalChartMap K)) }

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover

end

end


section
/- Whole official FLT proof at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Routine aliases expanded to standard opens; unused tool import and option headers omitted. Original forwarding dependencies point to the identical checked whole-source proofs. Named downstream consumer: actual order-13 scheme/place Cech comparison. -/
namespace P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one


open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

theorem solution {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by
  intro hX
  haveI : IsAffineHom f := isAffineHom_of_isAffine f
  haveI hfin : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

  have hΓ : (f.appTop).hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)

  let φ : k →+* Γ(X, ⊤) := (f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφfin : φ.Finite :=
    RingHom.Finite.comp hΓ (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfield : IsField Γ(X, ⊤) := by
    letI := φ.toAlgebra
    haveI : Module.Finite k Γ(X, ⊤) := hφfin
    haveI : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
    exact (Algebra.IsIntegral.isField_iff_isField (R := k) (S := Γ(X, ⊤)) φ.injective).mp
      (Field.toIsField k)

  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    haveI := Ring.isField_iff_isSimpleOrder_ideal.mp hfield
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top p.asIdeal with hp | hp
    · rcases IsSimpleOrder.eq_bot_or_eq_top q.asIdeal with hq | hq
      · rw [hp, hq]
      · exact absurd hq q.isPrime.ne_top
    · exact absurd hp p.isPrime.ne_top
  have hsubX : Subsingleton X := by
    haveI : Subsingleton (Spec Γ(X, ⊤)) := hsub
    exact (Scheme.homeoOfIso X.isoSpec).toEquiv.subsingleton
  have hclosed : IsClosed ({genericPoint X} : Set X) := by
    have : ({genericPoint X} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [this]; exact isClosed_univ

  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk (genericPoint X)) :=
    _root_.AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
      (genericPoint X) hclosed
  exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X))
    (Field.toIsField X.functionField)

end P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
#print axioms P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.solution

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual valuation places centered in the ordinary and
reciprocal affine opens of the unchanged order-13 sextic. Named downstream
consumer: the genuine scheme-section versus divisor-section Cech comparison.
The centers, complements, and intersection are proved; no genus is assumed.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem actual_curve_not_isAffine : ¬ IsAffine (curveScheme K) :=
  P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.solution
    (curveToBase K)

theorem actual_affineOpen_ne_top (U : (curveScheme K).Opens) (hU : IsAffineOpen U) :
    U ≠ ⊤ := by
  intro h
  have hT : IsAffineOpen (⊤ : (curveScheme K).Opens) := h ▸ hU
  haveI : IsAffine (⊤ : (curveScheme K).Opens) := hT
  exact actual_curve_not_isAffine K (IsAffine.of_isIso (curveScheme K).topIso.inv)

theorem actual_places_cover_nonempty_complements :
    placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0 ∪
        placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1 = Set.univ ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0) ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1) := by
  exact _root_.AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top
    (curveToBase K) (actualTwoAffineOpenCover K).U0 (actualTwoAffineOpenCover K).U1
    (actualTwoAffineOpenCover K).sup_eq_top
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U0)
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U1)

theorem actual_placesOf_inf (U V : (curveScheme K).Opens) :
    placesOf (curveToBase K) (U ⊓ V) =
      placesOf (curveToBase K) U ∩ placesOf (curveToBase K) V := by
  ext v
  constructor
  · rintro ⟨x, hx, hclosed, hrange⟩
    exact ⟨⟨x, hx.1, hclosed, hrange⟩, ⟨x, hx.2, hclosed, hrange⟩⟩
  · rintro ⟨⟨x, hxU, hxclosed, hxrange⟩, ⟨y, hyV, _, hyrange⟩⟩
    have hxy : x = y := _root_.AlgebraicCurve.eq_of_range_stalk_eq
      (curveToBase K) x y (hxrange.trans hyrange.symm)
    subst y
    exact ⟨x, ⟨hxU, hyV⟩, hxclosed, hxrange⟩

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_curve_not_isAffine
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_places_cover_nonempty_complements
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_placesOf_inf

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine affine coordinate sections of an open immersion
compatible with the base-field morphism. Named downstream consumer: the actual
order-thirteen chart/overlap section comparison with the official FLT cover.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace MazurTransfer.AffineOpenCoordinateSections
universe u
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of K))
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

theorem sectionsIso_inv :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE f.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE]

def sectionsRingIso : Γ(X, f.opensRange) ≅ CommRingCat.of A :=
  (IsOpenImmersion.ΓIsoTop f).symm ≪≫ Scheme.ΓSpecIso (.of A)

theorem sectionsRingIso_hom :
    (sectionsRingIso A f).hom = f.appLE f.opensRange ⊤ (by simp) ≫
      (Scheme.ΓSpecIso (.of A)).hom := by
  simp only [sectionsRingIso, Iso.trans_hom, Iso.symm_hom, sectionsIso_inv]

theorem sectionsRingIso_commutes
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    (Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ f.opensRange (by simp) ≫
      (sectionsRingIso A f).hom = CommRingCat.ofHom (algebraMap K A) := by
  have H : c.appLE ⊤ f.opensRange (by simp) ≫ f.appLE f.opensRange ⊤ (by simp) =
      (f ≫ c).appLE ⊤ ⊤ (by simp) :=
    Scheme.Hom.appLE_comp_appLE f c ⊤ f.opensRange ⊤ (by simp) (by simp)
  have H' : (f ≫ c).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop := by
    rw [hf]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ c).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of A)).hom := by
      rw [sectionsRingIso_hom]
      simpa only [Category.assoc] using congrArg
        (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := congrArg
          (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H'
    _ = _ := by rw [Scheme.ΓSpecIso_naturality]; simp

def sectionsAlgEquiv
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
    Γ(X, f.opensRange) ≃ₐ[K] A := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
  exact AlgEquiv.ofRingEquiv
    (f := (sectionsRingIso A f).commRingCatIsoToRingEquiv) (fun k =>
      congrArg (fun t => t.hom k) (sectionsRingIso_commutes K A c f hf))

variable {B : Type u} [CommRing B]

theorem sectionsRingIso_restriction (φ : A →+* B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hg : Spec.map (CommRingCat.ofHom φ) ≫ f = g)
    (hU : g.opensRange ≤ f.opensRange) :
    X.presheaf.map (Opposite.op (homOfLE hU)) ≫ (sectionsRingIso B g).hom =
      (sectionsRingIso A f).hom ≫ CommRingCat.ofHom φ := by
  have eg : (⊤ : (Spec (.of B)).Opens) ≤ g ⁻¹ᵁ f.opensRange := by
    simpa only [Scheme.Hom.preimage_opensRange] using g.preimage_mono hU
  have Hres : X.presheaf.map (homOfLE hU).op ≫ g.appLE g.opensRange ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := Scheme.Hom.map_appLE g (by simp) (homOfLE hU).op
  have Hcomp : f.appLE f.opensRange ⊤ (by simp) ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := by
    have H := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) f
      f.opensRange ⊤ ⊤ (by simp) (by simp)
    simpa only [hg] using H
  have Htop : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom φ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = g.appLE f.opensRange ⊤ eg ≫ (Scheme.ΓSpecIso (.of B)).hom := by
      rw [sectionsRingIso_hom]
      exact congrArg (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hres
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of B)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hcomp.symm
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Scheme.ΓSpecIso (.of B)).hom := congrArg
          (fun t => f.appLE f.opensRange ⊤ (by simp) ≫ t ≫
            (Scheme.ΓSpecIso (.of B)).hom) Htop
    _ = _ := by rw [Scheme.ΓSpecIso_naturality, sectionsRingIso_hom]; simp only [Category.assoc]

def sectionsAlgEquivAt (U : X.Opens) (hU : f.opensRange = U)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X, U) ≃ₐ[K] A := by
  subst U
  exact sectionsAlgEquiv K A c f hf

theorem sectionsAlgEquivAt_restriction [Algebra K B] (φ : A →ₐ[K] B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hgf : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = g)
    (U V : X.Opens) (hU : f.opensRange = U) (hV : g.opensRange = V) (hVU : V ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    ∀ z : Γ(X, U),
      sectionsAlgEquivAt K B c g V hV hg
        (Scheme.TwoAffineOpenCover.restrictAlgHom c hVU z) =
      φ (sectionsAlgEquivAt K A c f U hU hf z) := by
  subst U
  subst V
  intro z
  exact congrArg (fun t => t.hom z) (sectionsRingIso_restriction A f φ.toRingHom g hgf hVU)

end MazurTransfer.AffineOpenCoordinateSections
#print axioms MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquiv

#print axioms MazurTransfer.AffineOpenCoordinateSections.sectionsRingIso_restriction

#print axioms MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt_restriction

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine scheme intersection of the actual order-thirteen
charts, with the original overlap coordinate algebra and maps.
Named downstream consumer: actual structure-sheaf section comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K]

def ordinaryOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ XOneThirteenAffineCurve.scheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
    (OrdinaryOverlapRing K)))

def reciprocalOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ reciprocalScheme K :=
  Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase K).toRingHom)

def overlapToCurve : Spec (.of (OrdinaryOverlapRing K)) ⟶ curveScheme K :=
  ordinaryOverlapMap K ≫ ordinaryChartMap K

instance ordinaryOverlapMap_isOpenImmersion : IsOpenImmersion (ordinaryOverlapMap K) :=
  IsOpenImmersion.of_isLocalization (XOneThirteenAffineCurve.xCoordinate K)

instance overlapToCurve_isOpenImmersion : IsOpenImmersion (overlapToCurve K) := by
  unfold overlapToCurve
  infer_instance

theorem actual_overlap_isPullback :
    IsPullback (ordinaryOverlapMap K) (reciprocalOverlapMap K)
      (ordinaryChartMap K) (reciprocalChartMap K) := by
  classical
  have hne : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by decide
  have hnerev := Ne.symm hne
  have hv : (glueData K).V (Chart.ordinary, Chart.reciprocal) =
      Spec (.of (OrdinaryOverlapRing K)) := by
    simp only [glueData, CategoryTheory.GlueData.ofGlueData', categoricalGlueData, dif_neg hne]
  have H := IsPullback.of_isLimit
    ((glueData K).vPullbackConeIsLimit Chart.ordinary Chart.reciprocal)
  change IsPullback ((glueData K).f Chart.ordinary Chart.reciprocal)
    ((glueData K).t Chart.ordinary Chart.reciprocal ≫
      (glueData K).f Chart.reciprocal Chart.ordinary)
    (ordinaryChartMap K) (reciprocalChartMap K) at H
  have hmap : (overlapSchemeIso K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) = reciprocalOverlapMap K := by
    rw [overlapSchemeIso_hom, ← Spec.map_comp]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact reciprocalToOrdinary_algebraMap K a
  refine H.of_iso (eqToIso hv) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id,
      ordinaryOverlapMap, glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hne, overlapInclusion]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id,
      glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hne, dif_neg hnerev, overlapInclusion,
      overlapTransition, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hmap]
    rfl
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem overlapToCurve_eq_reciprocal :
    overlapToCurve K = reciprocalOverlapMap K ≫ reciprocalChartMap K :=
  (actual_overlap_isPullback K).w

theorem overlap_opensRange :
    (overlapToCurve K).opensRange = ordinaryOpen K ⊓ reciprocalOpen K := by
  have H := actual_overlap_isPullback K
  have he : H.isoPullback.hom ≫ pullback.fst (ordinaryChartMap K) (reciprocalChartMap K) ≫
      ordinaryChartMap K = overlapToCurve K := by
    rw [← Category.assoc, H.isoPullback_hom_fst]
    rfl
  apply TopologicalSpace.Opens.ext
  change Set.range (overlapToCurve K) =
    Set.range (ordinaryChartMap K) ∩ Set.range (reciprocalChartMap K)
  rw [← he]
  change Set.range ((pullback.fst (ordinaryChartMap K) (reciprocalChartMap K) ≫
    ordinaryChartMap K) ∘ H.isoPullback.hom) = _
  have hsurj : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact Scheme.Pullback.range_fst_comp _ _

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_overlap_isPullback
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.overlap_opensRange

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: an actual localized quadratic coordinate algebra is
equivalent to the quadratic algebra over Laurent polynomials. Named downstream
consumer: the two-chart Cech quotient of the order-thirteen curve.
This does not assert a genus or a sheaf-cohomology comparison.
-/

noncomputable section
namespace MazurTransfer.HyperellipticLaurentOverlap
open Polynomial

variable (K : Type*) [CommRing K] (f : Polynomial K)

instance : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      Polynomial.toLaurent_C]
    exact (LaurentPolynomial.C_eq_algebraMap k).symm

def equation : Polynomial (Polynomial K) := X ^ 2 - C f
abbrev Chart := AdjoinRoot (equation K f)
def x : Chart K f := AdjoinRoot.of (equation K f) X
def y : Chart K f := AdjoinRoot.root (equation K f)
abbrev Overlap := Localization.Away (x K f)
abbrev laurentEquation : Polynomial (LaurentPolynomial K) := X ^ 2 - C f.toLaurent
abbrev LaurentChart := AdjoinRoot (laurentEquation K f)

def toLaurentBase : Chart K f →ₐ[K] LaurentChart K f :=
  AdjoinRoot.liftAlgHom (equation K f)
    ((AdjoinRoot.ofAlgHom K (laurentEquation K f)).comp Polynomial.toLaurentAlg)
    (AdjoinRoot.root (laurentEquation K f)) (by
      have h := AdjoinRoot.eval₂_root (laurentEquation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact h)

@[simp] theorem toLaurentBase_x :
    toLaurentBase K f (x K f) =
      AdjoinRoot.of (laurentEquation K f) (LaurentPolynomial.T 1) := by
  simp [toLaurentBase, x]

@[simp] theorem toLaurentBase_y :
    toLaurentBase K f (y K f) = AdjoinRoot.root (laurentEquation K f) := by
  simp [toLaurentBase, y]

def toLaurent : Overlap K f →ₐ[K] LaurentChart K f :=
  IsLocalization.Away.liftAlgHom (x K f) (by
    rw [toLaurentBase_x]
    exact (LaurentPolynomial.isUnit_T (1 : ℤ)).map (AdjoinRoot.of (laurentEquation K f)))

@[simp] theorem toLaurent_algebraMap (a : Chart K f) :
    toLaurent K f (algebraMap (Chart K f) (Overlap K f) a) = toLaurentBase K f a := by
  simp [toLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

theorem coefficient_X_unit : IsUnit
    (((Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) X) := by
  change IsUnit (algebraMap (Chart K f) (Overlap K f) (x K f))
  exact IsLocalization.Away.algebraMap_isUnit (x K f)

def fromLaurentCoefficients : LaurentPolynomial K →ₐ[K] Overlap K f :=
  IsLocalization.Away.liftAlgHom (X : Polynomial K)
    (f := (Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) (coefficient_X_unit K f)

@[simp] theorem fromLaurentCoefficients_toLaurent (p : Polynomial K) :
    fromLaurentCoefficients K f p.toLaurent =
      algebraMap (Chart K f) (Overlap K f) (AdjoinRoot.of (equation K f) p) := by
  change fromLaurentCoefficients K f
    (algebraMap (Polynomial K) (LaurentPolynomial K) p) = _
  exact IsLocalization.Away.lift_eq (X : Polynomial K) (coefficient_X_unit K f) p

def fromLaurent : LaurentChart K f →ₐ[K] Overlap K f :=
  AdjoinRoot.liftAlgHom (laurentEquation K f) (fromLaurentCoefficients K f)
    (algebraMap (Chart K f) (Overlap K f) (y K f)) (by
      have h := AdjoinRoot.eval₂_root (equation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      have hm := congrArg (algebraMap (Chart K f) (Overlap K f)) h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change (algebraMap (Chart K f) (Overlap K f) (y K f)) ^ 2 -
        fromLaurentCoefficients K f f.toLaurent = 0
      rw [fromLaurentCoefficients_toLaurent]
      simpa only [map_sub, map_pow, map_zero, y] using hm)

@[simp] theorem fromLaurent_root :
    fromLaurent K f (AdjoinRoot.root (laurentEquation K f)) =
      algebraMap (Chart K f) (Overlap K f) (y K f) := by
  simp [fromLaurent]

theorem fromLaurent_comp_toLaurent :
    (fromLaurent K f).comp (toLaurent K f) = AlgHom.id K (Overlap K f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x K f))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (x K f))) =
      algebraMap (Chart K f) (Overlap K f) (x K f)
    rw [toLaurent_algebraMap, toLaurentBase_x]
    rw [← Polynomial.toLaurent_X]
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent]
    rfl
  · change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (y K f))) =
      algebraMap (Chart K f) (Overlap K f) (y K f)
    simp

theorem toLaurent_comp_fromLaurent :
    (toLaurent K f).comp (fromLaurent K f) = AlgHom.id K (LaurentChart K f) := by
  apply AdjoinRoot.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : Polynomial K))
    apply Polynomial.algHom_ext
    change toLaurent K f (fromLaurent K f (AdjoinRoot.of (laurentEquation K f)
      (Polynomial.toLaurent X))) = AdjoinRoot.of (laurentEquation K f) (Polynomial.toLaurent X)
    change toLaurent K f (AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _)) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent,
      toLaurent_algebraMap]
    simpa only [x, Polynomial.toLaurent_X] using toLaurentBase_x K f
  · simp

def overlapAlgEquiv : Overlap K f ≃ₐ[K] LaurentChart K f :=
  AlgEquiv.ofAlgHom (toLaurent K f) (fromLaurent K f)
    (toLaurent_comp_fromLaurent K f) (fromLaurent_comp_toLaurent K f)

end MazurTransfer.HyperellipticLaurentOverlap

#print axioms MazurTransfer.HyperellipticLaurentOverlap.overlapAlgEquiv

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: compute the quotient of Laurent coefficient pairs by the
two chart images with transitions x = z^-1 and y = w z^-3.
Named downstream consumer: the actual order-thirteen two-chart Cech quotient.
This algebraic coefficient calculation alone is not a genus theorem.
-/

noncomputable section
namespace MazurTransfer.LaurentTwoChartCoefficientQuotient

variable (K : Type*) [Field K]
abbrev LaurentCoefficients := ℤ →₀ K
abbrev ChartCoefficients := ℕ →₀ K
abbrev OverlapCoefficients := LaurentCoefficients K × LaurentCoefficients K

def ordinary : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ)))

def reciprocal : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ) - 3))

def boundaries : Submodule K (OverlapCoefficients K) := (ordinary K).range ⊔ (reciprocal K).range

def survivingCoefficients : OverlapCoefficients K →ₗ[K] K × K where
  toFun v := (v.2 (-1), v.2 (-2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem range_lmapDomain_eq_supported (e : ℕ → ℤ) :
    (Finsupp.lmapDomain K K e).range = Finsupp.supported K K (Set.range e) := by
  rw [Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single]
  congr 1
  ext z
  simp

theorem ordinary_range : (ordinary K).range =
    (Finsupp.supported K K {n : ℤ | 0 ≤ n}).prod
      (Finsupp.supported K K {n : ℤ | 0 ≤ n}) := by
  rw [ordinary, LinearMap.range_prodMap, range_lmapDomain_eq_supported]
  congr 2 <;> ext z <;> simp

theorem reciprocal_range : (reciprocal K).range =
    (Finsupp.supported K K {n : ℤ | n ≤ 0}).prod
      (Finsupp.supported K K {n : ℤ | n ≤ -3}) := by
  rw [reciprocal, LinearMap.range_prodMap, range_lmapDomain_eq_supported,
    range_lmapDomain_eq_supported]
  have h₀ : Set.range (fun n : ℕ => -(n : ℤ)) = {n : ℤ | n ≤ 0} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ 0 at hz
      refine ⟨(-z).toNat, ?_⟩
      change -((-z).toNat : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  have h₃ : Set.range (fun n : ℕ => -(n : ℤ) - 3) = {n : ℤ | n ≤ -3} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ -3 at hz
      refine ⟨(-z-3).toNat, ?_⟩
      change -((-z-3).toNat : ℤ) - 3 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  rw [h₀, h₃]

theorem boundaries_eq_kernel : boundaries K = (survivingCoefficients K).ker := by
  rw [boundaries, ordinary_range, reciprocal_range]
  apply le_antisymm
  · apply sup_le
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
  · intro v hv
    have hzero : v.2 (-1) = 0 ∧ v.2 (-2) = 0 := by
      change (v.2 (-1), v.2 (-2)) = (0, 0) at hv
      exact Prod.mk.inj hv
    let positive (a : ℤ →₀ K) := a.filter (fun n => 0 ≤ n)
    let negative (a : ℤ →₀ K) := a.filter (fun n => n < 0)
    refine Submodule.mem_sup.mpr ⟨(positive v.1, positive v.2), ?_,
      (negative v.1, negative v.2), ?_, ?_⟩
    · constructor <;> apply (Finsupp.mem_supported' K _).mpr <;>
        intro n hn <;> change ¬ 0 ≤ n at hn <;> simp [positive, hn]
    · constructor
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        simp [negative, show ¬ n < 0 by omega]
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        by_cases hp : 0 ≤ n
        · simp [negative, show ¬ n < 0 by omega]
        · have hn' : n = -1 ∨ n = -2 := by omega
          rcases hn' with rfl | rfl <;> simp [negative, hzero.1, hzero.2]
    · apply Prod.ext <;> ext n <;> by_cases hn : 0 ≤ n <;>
        simp [positive, negative, hn, show n < 0 ↔ ¬ 0 ≤ n by omega]

theorem survivingCoefficients_surjective : Function.Surjective (survivingCoefficients K) := by
  rintro ⟨a, b⟩
  let v : ℤ →₀ K := Finsupp.single (-1) a + Finsupp.single (-2) b
  refine ⟨(0, v), ?_⟩
  change (v (-1), v (-2)) = (a, b)
  simp [v]

def quotientEquiv : (OverlapCoefficients K ⧸ boundaries K) ≃ₗ[K] K × K :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_kernel K)).trans
    ((survivingCoefficients K).quotKerEquivOfSurjective (survivingCoefficients_surjective K))

theorem quotient_finrank : Module.finrank K (OverlapCoefficients K ⧸ boundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

end MazurTransfer.LaurentTwoChartCoefficientQuotient

#print axioms MazurTransfer.LaurentTwoChartCoefficientQuotient.quotient_finrank

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the quotient of the actual overlap coordinate algebra by
the sum of the images of the two actual chart algebras.
Named downstream consumer: comparison with genuine structure-sheaf H1.
This file makes no genus claim without that comparison.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCechQuotient
open Polynomial Module
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

variable (K : Type*) [Field K]
abbrev QuadraticLaurentRing := HyperellipticLaurentOverlap.LaurentChart K (sexticPolynomial K)

def overlapAlgEquiv : OrdinaryOverlapRing K ≃ₐ[K] QuadraticLaurentRing K :=
  HyperellipticLaurentOverlap.overlapAlgEquiv K (sexticPolynomial K)

def overlapCoordinates : OrdinaryOverlapRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.OverlapCoefficients K :=
  (overlapAlgEquiv K).toLinearEquiv.trans
    (((QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent).restrictScalars K).trans
      ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K)))

def ordinaryCoordinates : CoordinateRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

def reciprocalCoordinates : ReciprocalRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

theorem overlapCoordinates_of_add_of_mul_root (a b : LaurentPolynomial K) :
    overlapCoordinates K ((overlapAlgEquiv K).symm
      (AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) a +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) b *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)))) = (a.coeff, b.coeff) := by
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      ((overlapAlgEquiv K) ((overlapAlgEquiv K).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      (AdjoinRoot.of (QuadraticCoordinates.equation _ _) a + AdjoinRoot.of (QuadraticCoordinates.equation _ _) b *
        AdjoinRoot.root (QuadraticCoordinates.equation _ _))) = _
  rw [QuadraticCoordinates.coordinates_of_add_of_mul_root]
  rfl

theorem laurent_inverse_coordinate :
    overlapAlgEquiv K (IsLocalization.Away.invSelf (xCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  let o := AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
  have hu : IsUnit (o (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T (1 : ℤ)).map o
  apply hu.mul_left_cancel
  have hx : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (xCoordinate K)) =
      o (LaurentPolynomial.T 1) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.x K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_x K (sexticPolynomial K)
  rw [← hx, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, hx]
  change 1 = o (LaurentPolynomial.T 1) * o (LaurentPolynomial.T (-1))
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp only [Int.reduceAdd, LaurentPolynomial.T_zero, map_one]

theorem reciprocal_z_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  rw [reciprocalToOrdinaryBase_z]
  exact laurent_inverse_coordinate K

theorem reciprocal_w_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (wCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-3)) *
        AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  rw [reciprocalToOrdinaryBase_w]
  change overlapAlgEquiv K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3) = _
  rw [map_mul, map_pow, laurent_inverse_coordinate]
  have hy : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)
  rw [hy, ← map_pow, LaurentPolynomial.T_pow]
  norm_num only
  rw [mul_comm]

theorem invert_toLaurent_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ)) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]

theorem invert_toLaurent_shift_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent * LaurentPolynomial.T (-3)).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ) - 3) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]
      rfl

def actualBoundaries : Submodule K (OrdinaryOverlapRing K) :=
  (Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
    (reciprocalToOrdinaryBase K).toLinearMap.range

theorem ordinary_laurent (p : Polynomial K) :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
      (AdjoinRoot.of (affineEquation K) p)) =
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.toLaurent := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (AdjoinRoot.of (HyperellipticLaurentOverlap.equation K (sexticPolynomial K)) p)) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  simp [HyperellipticLaurentOverlap.toLaurentBase]

theorem ordinary_y_laurent :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)

theorem reciprocal_laurent (p : Polynomial K) :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (AdjoinRoot.of (reciprocalEquation K) p)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.toLaurent) := by
  have h : ((overlapAlgEquiv K).toAlgHom.comp (reciprocalToOrdinaryBase K)).comp
      (AdjoinRoot.ofAlgHom K (reciprocalEquation K)) =
    (AdjoinRoot.ofAlgHom K (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))).comp
      (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) := by
    apply Polynomial.algHom_ext
    change overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert (Polynomial.toLaurent (X : Polynomial K)))
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    exact reciprocal_z_laurent K
  exact DFunLike.congr_fun h p

theorem ordinary_diagram (a : CoordinateRing K) :
    overlapCoordinates K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      LaurentTwoChartCoefficientQuotient.ordinary K (ordinaryCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K) a
  have ha : a = AdjoinRoot.of (affineEquation K) p.1 +
      AdjoinRoot.of (affineEquation K) p.2 * yCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (sexticPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.1.toLaurent +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.2.toLaurent *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, ordinary_laurent, ordinary_laurent,
      ordinary_y_laurent]
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root]
  rfl

theorem reciprocal_diagram (a : ReciprocalRing K) :
    overlapCoordinates K (reciprocalToOrdinaryBase K a) =
      LaurentTwoChartCoefficientQuotient.reciprocal K (reciprocalCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
  have ha : a = AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (reciprocalToOrdinaryBase K a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.1.toLaurent) +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
          (LaurentPolynomial.invert p.2.toLaurent * LaurentPolynomial.T (-3)) *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, reciprocal_laurent, reciprocal_laurent,
      reciprocal_w_laurent, map_mul]
    ring
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root, invert_toLaurent_coeff,
    invert_toLaurent_shift_coeff]
  rfl

theorem actualBoundaries_image :
    (actualBoundaries K).map (overlapCoordinates K).toLinearMap =
      LaurentTwoChartCoefficientQuotient.boundaries K := by
  rw [actualBoundaries, LaurentTwoChartCoefficientQuotient.boundaries, Submodule.map_sup]
  congr 1
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨ordinaryCoordinates K a, (ordinary_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
        ((ordinaryCoordinates K).symm c), ⟨(ordinaryCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) ((ordinaryCoordinates K).symm c)) = _
      rw [ordinary_diagram, LinearEquiv.apply_symm_apply]
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨reciprocalCoordinates K a, (reciprocal_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c),
        ⟨(reciprocalCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c)) = _
      rw [reciprocal_diagram, LinearEquiv.apply_symm_apply]

def quotientEquiv : (OrdinaryOverlapRing K ⧸ actualBoundaries K) ≃ₗ[K] K × K :=
  (Submodule.Quotient.equiv (actualBoundaries K) (LaurentTwoChartCoefficientQuotient.boundaries K)
    (overlapCoordinates K) (actualBoundaries_image K)).trans
      (LaurentTwoChartCoefficientQuotient.quotientEquiv K)

theorem actual_two_chart_section_quotient_finrank :
    Module.finrank K (OrdinaryOverlapRing K ⧸ actualBoundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

def reciprocalPolynomialSections : (Polynomial K × Polynomial K) →ₗ[K] OrdinaryOverlapRing K :=
  let coeff := (Polynomial.aeval (IsLocalization.Away.invSelf (xCoordinate K)) :
    Polynomial K →ₐ[K] OrdinaryOverlapRing K).toLinearMap
  coeff.coprod ((LinearMap.mulRight K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3)).comp coeff)

theorem reciprocal_sections_formula (p : Polynomial K × Polynomial K) :
    reciprocalToOrdinaryBase K
      (AdjoinRoot.of (reciprocalEquation K) p.1 +
        AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K) =
      reciprocalPolynomialSections K p := by
  rw [map_add, map_mul]
  simp only [reciprocalToOrdinaryBase, AdjoinRoot.liftAlgHom_of,
    wCoordinate, AdjoinRoot.liftAlgHom_root]
  rfl

theorem reciprocal_polynomial_sections_range :
    (reciprocalToOrdinaryBase K).toLinearMap.range =
      (reciprocalPolynomialSections K).range := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
    refine ⟨p, ?_⟩
    rw [← reciprocal_sections_formula]
    apply congrArg (reciprocalToOrdinaryBase K)
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a)
  · rintro ⟨p, rfl⟩
    exact ⟨AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K,
      reciprocal_sections_formula K p⟩

theorem actual_quotient_finrank_polynomial_sections :
    Module.finrank K (OrdinaryOverlapRing K ⧸
      ((Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
        (reciprocalPolynomialSections K).range)) = 2 := by
  rw [← reciprocal_polynomial_sections_range]
  exact actual_two_chart_section_quotient_finrank K

end MazurTransfer.Order13ActualCechQuotient

#print axioms MazurTransfer.Order13ActualCechQuotient.overlapCoordinates
#print axioms MazurTransfer.Order13ActualCechQuotient.reciprocal_w_laurent
#print axioms MazurTransfer.Order13ActualCechQuotient.actual_two_chart_section_quotient_finrank
#print axioms MazurTransfer.Order13ActualCechQuotient.actual_quotient_finrank_polynomial_sections

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual structure-sheaf sections and restriction maps of the
original order-thirteen cover. Named downstream consumer: true Cech H1 dimension
and the audited official FLT scheme-to-genus comparison. No genus is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K]

abbrev sectionsCover := (actualTwoAffineOpenCover K).cover (curveToBase K)
abbrev actualStructureSheafSections := (actualTwoAffineOpenCover K).structureSheafSections (curveToBase K)

theorem overlapToCurve_curveToBase :
    overlapToCurve K ≫ curveToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (OrdinaryOverlapRing K))) := by
  rw [overlapToCurve, Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryOverlapMap ordinaryChartToBase
  rw [← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  exact IsScalarTower.algebraMap_eq K (XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)

def ordinarySectionsEquiv :
    (sectionsCover K).A0 ≃ₐ[K] XOneThirteenAffineCurve.CoordinateRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K
    (XOneThirteenAffineCurve.CoordinateRing K) (curveToBase K) (ordinaryChartMap K)
    (ordinaryOpen K) rfl (ordinaryChartMap_curveToBase K)

def reciprocalSectionsEquiv :
    (sectionsCover K).A1 ≃ₐ[K] ReciprocalRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K (ReciprocalRing K)
    (curveToBase K) (reciprocalChartMap K) (reciprocalOpen K) rfl (reciprocalChartMap_curveToBase K)

def overlapSectionsEquiv :
    (sectionsCover K).A01 ≃ₐ[K] OrdinaryOverlapRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K (OrdinaryOverlapRing K)
    (curveToBase K) (overlapToCurve K) (ordinaryOpen K ⊓ reciprocalOpen K)
    (overlap_opensRange K) (overlapToCurve_curveToBase K)

theorem ordinarySections_restrict (z : (sectionsCover K).A0) :
    overlapSectionsEquiv K ((sectionsCover K).ρ0 z) =
      algebraMap (XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)
        (ordinarySectionsEquiv K z) := by
  exact MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt_restriction K
    (XOneThirteenAffineCurve.CoordinateRing K) (curveToBase K) (ordinaryChartMap K)
    (Algebra.algHom K (XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K))
    (overlapToCurve K) (ordinaryChartMap_curveToBase K) (overlapToCurve_curveToBase K)
    rfl (ordinaryOpen K) (ordinaryOpen K ⊓ reciprocalOpen K) rfl (overlap_opensRange K)
    inf_le_left z

theorem reciprocalSections_restrict (z : (sectionsCover K).A1) :
    overlapSectionsEquiv K ((sectionsCover K).ρ1 z) =
      reciprocalToOrdinaryBase K (reciprocalSectionsEquiv K z) := by
  exact MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt_restriction K
    (ReciprocalRing K) (curveToBase K) (reciprocalChartMap K)
    (reciprocalToOrdinaryBase K) (overlapToCurve K) (reciprocalChartMap_curveToBase K)
    (overlapToCurve_curveToBase K) (overlapToCurve_eq_reciprocal K).symm
    (reciprocalOpen K) (ordinaryOpen K ⊓ reciprocalOpen K) rfl (overlap_opensRange K)
    inf_le_right z

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.ordinarySections_restrict
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.reciprocalSections_restrict

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual structure-sheaf Cech H1 for the unchanged scheme's
true two-affine-open cover. Named downstream consumer: the official FLT genus
comparison. No derived-cohomology comparison or genus theorem is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K]
open MazurTransfer.Order13ActualCechQuotient

def coordinateCechDiff :
    (XOneThirteenAffineCurve.CoordinateRing K × ReciprocalRing K) →ₗ[K] OrdinaryOverlapRing K :=
  (-(Algebra.algHom K (XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap).coprod
    (reciprocalToOrdinaryBase K).toLinearMap

theorem coordinateCechDiff_range : (coordinateCechDiff K).range = actualBoundaries K := by
  rw [coordinateCechDiff, LinearMap.range_coprod, LinearMap.range_neg]
  rfl

def chartSectionPairEquiv :
    ((actualStructureSheafSections K).M0 × (actualStructureSheafSections K).M1) ≃ₗ[K]
      (XOneThirteenAffineCurve.CoordinateRing K × ReciprocalRing K) :=
  (ordinarySectionsEquiv K).toLinearEquiv.prodCongr (reciprocalSectionsEquiv K).toLinearEquiv

theorem cechDiff_section_comparison
    (z : (actualStructureSheafSections K).M0 × (actualStructureSheafSections K).M1) :
    overlapSectionsEquiv K ((actualStructureSheafSections K).cechDiff z) =
      coordinateCechDiff K (chartSectionPairEquiv K z) := by
  rw [TwoChartCech.Sections.cechDiff_apply, map_sub]
  change overlapSectionsEquiv K (((1 : (sectionsCover K).A01ˣ) : (sectionsCover K).A01) *
    (sectionsCover K).ρ1 z.2) -
    overlapSectionsEquiv K ((sectionsCover K).ρ0 z.1) = _
  rw [Units.val_one, one_mul, reciprocalSections_restrict, ordinarySections_restrict]
  simp [coordinateCechDiff, chartSectionPairEquiv, sub_eq_add_neg, add_comm]
  rfl

theorem cechDiff_range_section_comparison :
    Submodule.map (overlapSectionsEquiv K).toLinearEquiv.toLinearMap
      (actualStructureSheafSections K).cechDiff.range = actualBoundaries K := by
  rw [← coordinateCechDiff_range K]
  ext y
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨chartSectionPairEquiv K z, (cechDiff_section_comparison K z).symm⟩
  · rintro ⟨z, rfl⟩
    let w := (chartSectionPairEquiv K).symm z
    refine ⟨(actualStructureSheafSections K).cechDiff w, ⟨w, rfl⟩, ?_⟩
    change overlapSectionsEquiv K ((actualStructureSheafSections K).cechDiff w) = _
    rw [cechDiff_section_comparison, LinearEquiv.apply_symm_apply]

def actualStructureSheafH1Equiv :
    (actualStructureSheafSections K).H1 ≃ₗ[K] (OrdinaryOverlapRing K ⧸ actualBoundaries K) :=
  Submodule.Quotient.equiv _ _ (overlapSectionsEquiv K).toLinearEquiv
    (cechDiff_range_section_comparison K)

theorem actual_structureSheaf_cechH1_finrank :
    Module.finrank K (actualStructureSheafSections K).H1 = 2 := by
  rw [(actualStructureSheafH1Equiv K).finrank_eq]
  exact actual_two_chart_section_quotient_finrank K

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.cechDiff_section_comparison
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_structureSheaf_cechH1_finrank

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: cohomology of the actual valuation-place cover of the original
order-13 curve. Named downstream consumer: the genuine FLT Cech-to-repartitions
H1 comparison. The section-to-place comparison retains the complete official
proof at FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2. No genus assertion
or Riemann-Roch existence assumption is used in this dimension calculation.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem actual_cover_open_nonempty (U V : (curveScheme K).Opens)
    (hUV : U ⊔ V = ⊤) (hV : IsAffineOpen V) : Nonempty U := by
  have hUne : (U : Set (curveScheme K)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := TopologicalSpace.Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact actual_affineOpen_ne_top K V hV hUV
  exact hUne.to_subtype

abbrev actualPlaceCechH1 : Type u :=
  cechH1 (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0)
    (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1)
    (0 : Divisor K (actualCurveFunctionField K))

theorem actual_structureSheaf_placeCechH1_equiv :
    Nonempty ((actualStructureSheafSections K).H1 ≃ₗ[K] actualPlaceCechH1 K) := by
  have h0 := actual_cover_open_nonempty K _ _
    (actualTwoAffineOpenCover K).sup_eq_top
    (actualTwoAffineOpenCover K).isAffineOpen_U1
  have h1 := actual_cover_open_nonempty K _ _
    ((sup_comm _ _).trans (actualTwoAffineOpenCover K).sup_eq_top)
    (actualTwoAffineOpenCover K).isAffineOpen_U0
  exact (_root_.AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1
    (actualTwoAffineOpenCover K) (curveToBase K) h0 h1).2

theorem actual_placeCechH1_finrank : Module.finrank K (actualPlaceCechH1 K) = 2 := by
  obtain ⟨e⟩ := actual_structureSheaf_placeCechH1_equiv K
  exact e.finrank_eq.symm.trans (actual_structureSheaf_cechH1_finrank K)

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_structureSheaf_placeCechH1_equiv
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_placeCechH1_finrank

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the genuine global repartition cohomology of the original
order-13 curve. Named downstream consumer: actual genus comparison. The original
IsCurveOver, finite constant-function space, and RiemannGenusReachedAt hypotheses
remain explicit. This bridge does not assert that those inputs have been proved.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem actual_globalH1_finrank_of_genusReached
    [IsCurveOver K (actualCurveFunctionField K)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K (actualCurveFunctionField K)))]
    {γ : ℤ} {D₀ : Divisor K (actualCurveFunctionField K)}
    (h : RiemannGenusReachedAt γ D₀) :
    Module.finrank K (H1 (0 : Divisor K (actualCurveFunctionField K))) = 2 := by
  obtain ⟨hcover, h₀, h₁⟩ := actual_places_cover_nonempty_complements K
  let e : actualPlaceCechH1 K ≃ₗ[K] H1 (0 : Divisor K (actualCurveFunctionField K)) :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover 0)
      (cechH1ToH1_bijective h hcover h₀ h₁ 0)
  exact e.finrank_eq.symm.trans (actual_placeCechH1_finrank K)

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_globalH1_finrank_of_genusReached

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the genuine FLT repartition genus of the actual order-13
curve's function field over an algebraically closed field of characteristic
zero. Named downstream consumer: the modular curve/Picard/Jacobian bridge.
IsCurveOver, constant-field equality and Riemann–Roch existence are derived
from the unchanged curve; none is assumed as an additional hypothesis.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

instance actualFunctionFieldEssFiniteType :
    Algebra.EssFiniteType K (actualCurveFunctionField K) :=
  _root_.AlgebraicCurve.essFiniteType_functionField (curveToBase K)

theorem actual_constantsAreBase [IsAlgClosed K] :
    ConstantsAreBase K (actualCurveFunctionField K) := by
  obtain ⟨_, ⟨v, _⟩, _⟩ := actual_places_cover_nonempty_complements K
  exact constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)

theorem actual_stichtenothGenusExists [IsAlgClosed K] :
    StichtenothGenusExists K (actualCurveFunctionField K) :=
  stichtenothGenusExists_of_isCurveOver (actual_constantsAreBase K)

theorem actual_genusFF_eq_two [IsAlgClosed K] :
    genusFF K (actualCurveFunctionField K) = 2 := by
  obtain ⟨_, hfinite, γ, D₀, hgenus⟩ := actual_stichtenothGenusExists K
  letI := hfinite
  exact actual_globalH1_finrank_of_genusReached K hgenus

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualFunctionFieldEssFiniteType
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_constantsAreBase
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_stichtenothGenusExists
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_genusFF_eq_two

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual rational place centered at the literal affine
point (0,1) of the unchanged order-13 curve. Named downstream consumer:
unconditional characteristic-zero constant-field and function-field genus
comparison, including the rational base field needed for the arithmetic work.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

def actualZeroOneAffineHom : XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K :=
  XOneThirteenAffineCurve.solutionToAlgHom K
    ⟨(0, 1), by simp [XOneThirteenAffineCurve.sexticPolynomial]⟩

def actualZeroOneSection : Spec (.of K) ⟶ curveScheme K :=
  Spec.map (CommRingCat.ofHom (actualZeroOneAffineHom K).toRingHom) ≫ ordinaryChartMap K

theorem actualZeroOneSection_over_base :
    actualZeroOneSection K ≫ curveToBase K = 𝟙 _ := by
  unfold actualZeroOneSection
  rw [Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap K (XOneThirteenAffineCurve.CoordinateRing K)) ≫
      CommRingCat.ofHom (actualZeroOneAffineHom K).toRingHom = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext k
    exact (actualZeroOneAffineHom K).commutes k
  rw [h, Spec.map_id]

theorem actualZeroOnePoint_isClosed :
    IsClosed ({(actualZeroOneSection K).base (IsLocalRing.closedPoint K)} : Set (curveScheme K)) := by
  haveI : IsClosedImmersion (actualZeroOneSection K ≫ curveToBase K) := by
    rw [actualZeroOneSection_over_base]
    infer_instance
  haveI : IsClosedImmersion (actualZeroOneSection K) :=
    IsClosedImmersion.of_comp (actualZeroOneSection K) (curveToBase K)
  have h := (actualZeroOneSection K).isClosedEmbedding.isClosedMap
    {IsLocalRing.closedPoint K} isClosed_singleton
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨IsLocalRing.closedPoint K, Set.mem_singleton _, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).symm
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact Set.mem_singleton _

def actualZeroOneClosedPoint : closedPoints (curveScheme K) :=
  ⟨(actualZeroOneSection K).base (IsLocalRing.closedPoint K),
    mem_closedPoints_iff.mpr (actualZeroOnePoint_isClosed K)⟩

def actualZeroOnePlace : Place K (actualCurveFunctionField K) :=
  actualPlaceOfPoint K (actualZeroOneClosedPoint K)

theorem actualZeroOnePlace_isRational : (actualZeroOnePlace K).IsRational :=
  Place.isRational_of_range_stalk_section_eq (curveToBase K)
    (actualZeroOneSection K) (actualZeroOneSection_over_base K)
    (actualZeroOnePlace K) (actualPlaceOfPoint_stalk_range K (actualZeroOneClosedPoint K))

theorem actualZeroOnePlace_deg : (actualZeroOnePlace K).deg = 1 :=
  ((actualZeroOnePlace K).isRational_iff_deg_eq_one).mp (actualZeroOnePlace_isRational K)

theorem actual_constantsAreBase_charZero : ConstantsAreBase K (actualCurveFunctionField K) :=
  constantsAreBase_of_deg_eq_one (actualZeroOnePlace K) (actualZeroOnePlace_deg K)

theorem actual_stichtenothGenusExists_charZero :
    StichtenothGenusExists K (actualCurveFunctionField K) :=
  stichtenothGenusExists_of_isCurveOver (actual_constantsAreBase_charZero K)

theorem actual_genusFF_eq_two_charZero : genusFF K (actualCurveFunctionField K) = 2 := by
  obtain ⟨_, hfinite, γ, D₀, hgenus⟩ := actual_stichtenothGenusExists_charZero K
  letI := hfinite
  exact actual_globalH1_finrank_of_genusReached K hgenus

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualZeroOneSection_over_base
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actualZeroOnePlace_isRational
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.actual_genusFF_eq_two_charZero

end

end

theorem solution.{u} (K : Type u) [Field K] [CharZero K] :
    ∃ (hC : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K)),
      letI := hC
      letI := (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
      AlgebraicCurve.genusFF K
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField = 2 := by
  refine ⟨inferInstance, ?_⟩
  exact MazurTorsion.XOneThirteenProjectiveCurve.actual_genusFF_eq_two_charZero K
#print axioms solution
