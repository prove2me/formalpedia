-- Prove2me | solution 1 for MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T04:23:35.621629+00:00
-- url     : https://prove2.me/submissions/d9516a22-25d3-4143-9d7f-213ccfe29fc7

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the checked square-zero differential construction of
IntegralHyperellipticCoordinateDifferentials to a mixed quadratic equation.
Design boundary: actual Kaehler differentials are free of rank one when the
two coordinate partials generate the unit ideal, without inverting two.
Named downstream consumer: dyadic mixed chart relative dimension one.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateDifferentialsProof
open Polynomial Module
variable (K : Type*) [CommRing K] (h f : Polynomial K)
abbrev equation : Polynomial (Polynomial K) := X ^ 2 + C h * X - C f
abbrev CoordinateRing := AdjoinRoot (equation K h f)
def x : CoordinateRing K h f := AdjoinRoot.of (equation K h f) X
def y : CoordinateRing K h f := AdjoinRoot.root (equation K h f)
abbrev of : Polynomial K →+* CoordinateRing K h f := AdjoinRoot.of (equation K h f)
def partialX : CoordinateRing K h f := of K h f h.derivative * y K h f - of K h f f.derivative
def partialY : CoordinateRing K h f := 2 * y K h f + of K h f h

theorem root_relation : y K h f ^ 2 + of K h f h * y K h f - of K h f f = 0 := by
  have ht := AdjoinRoot.eval₂_root (equation K h f)
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] at ht
  exact ht

theorem of_eq_aeval (p : Polynomial K) : of K h f p = aeval (x K h f) p := by
  have ht : AdjoinRoot.ofAlgHom K (equation K h f) = aeval (x K h f) := by
    apply Polynomial.algHom_ext
    simp [x]
  exact DFunLike.congr_fun ht p

abbrev Dual := TrivSqZeroExt (CoordinateRing K h f) (CoordinateRing K h f)

theorem aeval_dual (p : Polynomial K) (a da : CoordinateRing K h f) :
    aeval (TrivSqZeroExt.inl a + TrivSqZeroExt.inr da : Dual K h f) p =
      TrivSqZeroExt.inl (aeval a p) + TrivSqZeroExt.inr (aeval a p.derivative * da) := by
  have hsq : (TrivSqZeroExt.inr da : Dual K h f) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have hmap : (TrivSqZeroExt.inlAlgHom K (CoordinateRing K h f) (CoordinateRing K h f)).comp
      (aeval a) = aeval (TrivSqZeroExt.inl a : Dual K h f) := by
    apply Polynomial.algHom_ext
    simp
  rw [aeval_add_of_sq_eq_zero p _ _ hsq]
  rw [← DFunLike.congr_fun hmap p, ← DFunLike.congr_fun hmap p.derivative]
  change TrivSqZeroExt.inl (aeval a p) +
    TrivSqZeroExt.inl (aeval a p.derivative) * TrivSqZeroExt.inr da = _
  rw [TrivSqZeroExt.inl_mul_inr]
  rfl

def dualX : Dual K h f := TrivSqZeroExt.inl (x K h f) + TrivSqZeroExt.inr (partialY K h f)
def dualY : Dual K h f := TrivSqZeroExt.inl (y K h f) + TrivSqZeroExt.inr (-partialX K h f)

theorem dual_relation :
    dualY K h f ^ 2 + aeval (dualX K h f) h * dualY K h f - aeval (dualX K h f) f = 0 := by
  rw [dualX, aeval_dual, aeval_dual]
  apply TrivSqZeroExt.ext
  · simpa [dualY, pow_two, ← of_eq_aeval] using root_relation K h f
  · simp only [dualY, pow_two, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      ← of_eq_aeval, smul_eq_mul, op_smul_eq_smul, TrivSqZeroExt.snd_zero]
    dsimp only [partialX, partialY]
    ring

def dualSection : CoordinateRing K h f →ₐ[K] Dual K h f :=
  AdjoinRoot.liftAlgHom (equation K h f) (aeval (dualX K h f)) (dualY K h f) (by
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    exact dual_relation K h f)

@[simp] theorem dualSection_x : dualSection K h f (x K h f) = dualX K h f := by
  simp [dualSection, x]
@[simp] theorem dualSection_y : dualSection K h f (y K h f) = dualY K h f := by
  simp [dualSection, y]

theorem dualSection_fst :
    (TrivSqZeroExt.fstHom K (CoordinateRing K h f) (CoordinateRing K h f)).comp
      (dualSection K h f) = AlgHom.id K (CoordinateRing K h f) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change (dualSection K h f (x K h f)).fst = x K h f
    rw [dualSection_x]
    simp [dualX]
  · change (dualSection K h f (y K h f)).fst = y K h f
    rw [dualSection_y]
    simp [dualY]

def tangentDerivation : Derivation K (CoordinateRing K h f) (CoordinateRing K h f) where
  toLinearMap := ((TrivSqZeroExt.sndHom (CoordinateRing K h f) (CoordinateRing K h f)).restrictScalars K).comp
    (dualSection K h f).toLinearMap
  map_one_eq_zero' := by change (dualSection K h f 1).snd = 0; simp
  leibniz' a b := by
    change (dualSection K h f (a * b)).snd =
      a • (dualSection K h f b).snd + b • (dualSection K h f a).snd
    have ha : (dualSection K h f a).fst = a := DFunLike.congr_fun (dualSection_fst K h f) a
    have hb : (dualSection K h f b).fst = b := DFunLike.congr_fun (dualSection_fst K h f) b
    rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb]
    simp [smul_eq_mul, mul_comm]

@[simp] theorem tangentDerivation_x : tangentDerivation K h f (x K h f) = partialY K h f := by
  change (dualSection K h f (x K h f)).snd = _
  rw [dualSection_x]
  simp [dualX]
@[simp] theorem tangentDerivation_y : tangentDerivation K h f (y K h f) = -partialX K h f := by
  change (dualSection K h f (y K h f)).snd = _
  rw [dualSection_y]
  simp [dualY]

theorem derivation_of {M : Type*} [AddCommGroup M] [Module (CoordinateRing K h f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K h f) M]
    (d : Derivation K (CoordinateRing K h f) M) (p : Polynomial K) :
    d (of K h f p) = of K h f p.derivative • d (x K h f) := by
  rw [of_eq_aeval, d.map_aeval, ← of_eq_aeval]

theorem derivation_relation {M : Type*} [AddCommGroup M] [Module (CoordinateRing K h f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K h f) M]
    (d : Derivation K (CoordinateRing K h f) M) :
    partialX K h f • d (x K h f) + partialY K h f • d (y K h f) = 0 := by
  have ht := congrArg d (root_relation K h f)
  simp only [pow_two, d.map_sub, d.map_add, d.leibniz, derivation_of, map_zero] at ht
  calc
    _ = (y K h f • d (y K h f) + y K h f • d (y K h f) +
      (of K h f h • d (y K h f) + y K h f • (of K h f h.derivative • d (x K h f))) -
      of K h f f.derivative • d (x K h f)) := by dsimp only [partialX, partialY]; module
    _ = 0 := ht

private theorem unimodular_generator {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (U V a b : A) (dx dy : M) (hab : a * U + b * V = 1) (hrel : U • dx + V • dy = 0) :
    V • (b • dx - a • dy) = dx ∧ (-U) • (b • dx - a • dy) = dy := by
  have hU : U • dx = -(V • dy) := eq_neg_iff_add_eq_zero.mpr hrel
  have hV : V • dy = -(U • dx) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hrel)
  have hcoef : b * V + a * U = 1 := by rw [add_comm]; exact hab
  constructor
  · calc
      _ = (b * V) • dx - a • (V • dy) := by module
      _ = (b * V + a * U) • dx := by rw [hV]; module
      _ = dx := by rw [hcoef, one_smul]
  · calc
      _ = -b • (U • dx) + (a * U) • dy := by module
      _ = (b * V + a * U) • dy := by rw [hU]; module
      _ = dy := by rw [hcoef, one_smul]

theorem kaehler_equiv (hjac : ∃ a b : CoordinateRing K h f,
    a * partialX K h f + b * partialY K h f = 1) :
    Nonempty (Ω[CoordinateRing K h f⁄K] ≃ₗ[CoordinateRing K h f] CoordinateRing K h f) := by
  obtain ⟨a, b, hab⟩ := hjac
  let A := CoordinateRing K h f
  let d := KaehlerDifferential.D K A
  let w : Ω[A⁄K] := b • d (x K h f) - a • d (y K h f)
  have hxy := unimodular_generator (partialX K h f) (partialY K h f) a b
    (d (x K h f)) (d (y K h f)) hab (derivation_relation K h f d)
  have hx : partialY K h f • w = d (x K h f) := hxy.1
  have hy : (-partialX K h f) • w = d (y K h f) := hxy.2
  let W := Submodule.span A ({w} : Set Ω[A⁄K])
  have hw : w ∈ W := Submodule.subset_span (Set.mem_singleton w)
  have hdx : d (x K h f) ∈ W := hx ▸ W.smul_mem _ hw
  have hdy : d (y K h f) ∈ W := hy ▸ W.smul_mem _ hw
  have hspan : W = ⊤ := by
    apply top_unique
    rw [← KaehlerDifferential.span_range_derivation K A]
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    induction p using Polynomial.induction_on with
    | C q =>
      change d (of K h f q) ∈ W
      rw [derivation_of]
      exact W.smul_mem _ hdx
    | add p q hp hq =>
      rw [map_add, d.map_add]
      exact W.add_mem hp hq
    | monomial n q hn =>
      have he : C q * X ^ (n + 1) = (C q * X ^ n) * X := by rw [pow_succ, mul_assoc]
      rw [he, map_mul, AdjoinRoot.mk_X, d.leibniz]
      exact W.add_mem (W.smul_mem _ hdy) (W.smul_mem _ hn)
  let l : Ω[A⁄K] →ₗ[A] A := (tangentDerivation K h f).liftKaehlerDifferential
  have hl : l w = 1 := by
    change (tangentDerivation K h f).liftKaehlerDifferential
      (b • KaehlerDifferential.D K A (x K h f) - a • KaehlerDifferential.D K A (y K h f)) = 1
    rw [map_sub, map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, tangentDerivation_x, tangentDerivation_y]
    simp only [smul_eq_mul]
    calc
      _ = a * partialX K h f + b * partialY K h f := by ring
      _ = 1 := hab
  have hinj : Function.Injective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    intro r s hrs
    have hh := congrArg l hrs
    simpa only [LinearMap.toSpanSingleton_apply, map_smul, hl, smul_eq_mul, mul_one] using hh
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact hspan
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton A Ω[A⁄K] w) ⟨hinj, hsurj⟩).symm⟩

end MazurTransfer.MixedQuadraticCoordinateDifferentialsProof

theorem solution
    (R : Type*) [CommRing R] (h f : Polynomial R)
    (hjac : ∃ a b : AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)),
      a * (AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h.derivative *
        AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) -
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) f.derivative) +
      b * (2 * AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) +
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h) = 1) :
    Nonempty (Ω[AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))⁄R] ≃ₗ[AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))] AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))) := by
  exact MazurTransfer.MixedQuadraticCoordinateDifferentialsProof.kaehler_equiv R h f hjac
#print axioms solution
