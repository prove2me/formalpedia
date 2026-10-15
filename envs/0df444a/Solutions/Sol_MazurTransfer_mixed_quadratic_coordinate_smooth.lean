-- Prove2me | solution 1 for MazurTransfer.mixed_quadratic_coordinate_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T00:11:02.795773+00:00
-- url     : https://prove2.me/submissions/bfb01c55-dbeb-494f-97ea-bf37a8ae3bc1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Self-contained owned proof for the mixed quadratic coordinate smoothness
interface, used by the order-thirteen integral charts at two.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateSmoothProof
open Polynomial
universe u v
variable (R : Type u) [CommRing R]

def equation (h f : Polynomial R) : Polynomial (Polynomial R) := X ^ 2 + C h * X - C f
abbrev CoordinateRing (h f : Polynomial R) := AdjoinRoot (equation R h f)

def partialX (h f : Polynomial R) : CoordinateRing R h f :=
  AdjoinRoot.of (equation R h f) h.derivative * AdjoinRoot.root (equation R h f) -
    AdjoinRoot.of (equation R h f) f.derivative

def partialY (h f : Polynomial R) : CoordinateRing R h f :=
  2 * AdjoinRoot.root (equation R h f) + AdjoinRoot.of (equation R h f) h

theorem root_relation (h f : Polynomial R) :
    AdjoinRoot.root (equation R h f) ^ 2 +
      AdjoinRoot.of (equation R h f) h * AdjoinRoot.root (equation R h f) -
      AdjoinRoot.of (equation R h f) f = 0 := by
  have ht := AdjoinRoot.eval₂_root (equation R h f)
  change eval₂ (AdjoinRoot.of (equation R h f)) (AdjoinRoot.root (equation R h f))
    (X ^ 2 + C h * X - C f) = 0 at ht
  simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using ht

variable {B : Type v} [CommRing B] [Algebra R B]

theorem correction_error (h f : Polynomial R) (x y dx dy : B)
    (hdx : dx ^ 2 = 0) (hdy : dy ^ 2 = 0) (hxy : dx * dy = 0) :
    (y + dy) ^ 2 + aeval (x + dx) h * (y + dy) - aeval (x + dx) f =
      (y ^ 2 + aeval x h * y - aeval x f) +
        (aeval x h.derivative * y - aeval x f.derivative) * dx +
        (2 * y + aeval x h) * dy := by
  rw [aeval_add_of_sq_eq_zero h x dx hdx, aeval_add_of_sq_eq_zero f x dx hdx]
  calc
    _ = (y ^ 2 + aeval x h * y - aeval x f) +
        (aeval x h.derivative * y - aeval x f.derivative) * dx +
        (2 * y + aeval x h) * dy + dy ^ 2 + aeval x h.derivative * (dx * dy) := by ring
    _ = _ := by rw [hdy, hxy]; ring

end MazurTransfer.MixedQuadraticCoordinateSmoothProof

noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateSmoothProof
open Polynomial
universe u
variable (R : Type u) [CommRing R] (h f : Polynomial R)

theorem coordinate_smooth
    (hjac : ∃ a b : CoordinateRing R h f,
      a * partialX R h f + b * partialY R h f = 1) :
    Algebra.Smooth R (CoordinateRing R h f) := by
  let q := equation R h f
  obtain ⟨a, b, hab⟩ := hjac
  have hroot := root_relation R h f
  have : Algebra.FormallySmooth R (AdjoinRoot q) := by
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI φ
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.of q X))
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.root q))
    obtain ⟨av, hav⟩ := Ideal.Quotient.mk_surjective (φ a)
    obtain ⟨bv, hbv⟩ := Ideal.Quotient.mk_surjective (φ b)
    have hφpoly : φ.comp (AdjoinRoot.ofAlgHom R q) =
        aeval (φ (AdjoinRoot.of q X)) := by
      apply Polynomial.algHom_ext
      simp
    have hφeval (p : Polynomial R) : φ (AdjoinRoot.of q p) =
        aeval (φ (AdjoinRoot.of q X)) p := DFunLike.congr_fun hφpoly p
    have hφrelation : φ (AdjoinRoot.root q) ^ 2 +
        aeval (φ (AdjoinRoot.of q X)) h * φ (AdjoinRoot.root q) -
        aeval (φ (AdjoinRoot.of q X)) f = 0 := by
      have ht := congrArg φ hroot
      rw [_root_.map_sub, _root_.map_add, _root_.map_mul, _root_.map_pow,
        _root_.map_zero, hφeval h, hφeval f] at ht
      exact ht
    have hmap : (Ideal.Quotient.mkₐ R I).comp (aeval x) =
        aeval (Ideal.Quotient.mk I x) := by
      apply Polynomial.algHom_ext
      simp
    have hmapval (p : Polynomial R) : Ideal.Quotient.mkₐ R I (aeval x p) =
        aeval (Ideal.Quotient.mk I x) p := DFunLike.congr_fun hmap p
    let e : B := y ^ 2 + aeval x h * y - aeval x f
    have he0 : Ideal.Quotient.mkₐ R I e = 0 := by
      change Ideal.Quotient.mkₐ R I (y ^ 2 + aeval x h * y - aeval x f) = 0
      rw [_root_.map_sub, _root_.map_add, _root_.map_pow, _root_.map_mul, hmapval, hmapval]
      change Ideal.Quotient.mk I y ^ 2 + aeval (Ideal.Quotient.mk I x) h *
        Ideal.Quotient.mk I y - aeval (Ideal.Quotient.mk I x) f = 0
      rw [hx, hy, hφrelation]
    have heI : e ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp he0
    have sqzero {z w : B} (hz : z ∈ I) (hw : w ∈ I) : z * w = 0 := by
      have ht := Ideal.mul_mem_mul hz hw
      rw [← pow_two, hI] at ht
      exact ht
    let jx : B := aeval x h.derivative * y - aeval x f.derivative
    let jy : B := 2 * y + aeval x h
    have hjx : Ideal.Quotient.mkₐ R I jx = φ (partialX R h f) := by
      change Ideal.Quotient.mkₐ R I (aeval x h.derivative * y - aeval x f.derivative) =
        φ (AdjoinRoot.of q h.derivative * AdjoinRoot.root q - AdjoinRoot.of q f.derivative)
      rw [_root_.map_sub, _root_.map_mul, hmapval, hmapval]
      change aeval (Ideal.Quotient.mk I x) h.derivative * Ideal.Quotient.mk I y -
        aeval (Ideal.Quotient.mk I x) f.derivative = _
      rw [hx, hy, _root_.map_sub, _root_.map_mul, hφeval h.derivative, hφeval f.derivative]
    have hjy : Ideal.Quotient.mkₐ R I jy = φ (partialY R h f) := by
      change Ideal.Quotient.mkₐ R I (2 * y + aeval x h) =
        φ (2 * AdjoinRoot.root q + AdjoinRoot.of q h)
      rw [_root_.map_add, _root_.map_mul, _root_.map_ofNat, hmapval]
      change 2 * Ideal.Quotient.mk I y + aeval (Ideal.Quotient.mk I x) h = _
      rw [hx, hy, _root_.map_add, _root_.map_mul, _root_.map_ofNat, hφeval h]
    have hjacmod : Ideal.Quotient.mkₐ R I (av * jx + bv * jy) = 1 := by
      calc
        _ = φ (a * partialX R h f + b * partialY R h f) := by
          have hav' : Ideal.Quotient.mkₐ R I av = φ a := hav
          have hbv' : Ideal.Quotient.mkₐ R I bv = φ b := hbv
          rw [_root_.map_add, _root_.map_mul, _root_.map_mul, hav', hbv', hjx, hjy,
            _root_.map_add, _root_.map_mul, _root_.map_mul]
        _ = 1 := by rw [hab, _root_.map_one]
    let delta : B := 1 - (av * jx + bv * jy)
    have hdeltaI : delta ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change Ideal.Quotient.mkₐ R I (1 - (av * jx + bv * jy)) = 0
      rw [_root_.map_sub, _root_.map_one, hjacmod, sub_self]
    let dx : B := -(e * av)
    let dy : B := -(e * bv)
    have hdxI : dx ∈ I := I.neg_mem (I.mul_mem_right av heI)
    have hdyI : dy ∈ I := I.neg_mem (I.mul_mem_right bv heI)
    have hdx2 : dx ^ 2 = 0 := by rw [pow_two]; exact sqzero hdxI hdxI
    have hdy2 : dy ^ 2 = 0 := by rw [pow_two]; exact sqzero hdyI hdyI
    have hlift : (y + dy) ^ 2 + aeval (x + dx) h * (y + dy) - aeval (x + dx) f = 0 := by
      rw [correction_error R h f x y dx dy hdx2 hdy2 (sqzero hdxI hdyI)]
      calc
        _ = e * delta := by dsimp [e, delta, jx, jy, dx, dy]; ring
        _ = 0 := sqzero heI hdeltaI
    let ψ : AdjoinRoot q →ₐ[R] B :=
      AdjoinRoot.liftAlgHom q (aeval (x + dx)) (y + dy) (by
        change eval₂ (aeval (x + dx)).toRingHom (y + dy)
          (X ^ 2 + C h * X - C f) = 0
        simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
        change (y + dy) ^ 2 + aeval (x + dx) h * (y + dy) - aeval (x + dx) f = 0
        exact hlift)
    refine ⟨ψ, ?_⟩
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom, ψ,
        AdjoinRoot.liftAlgHom_of, aeval_X]
      change Ideal.Quotient.mk I (x + dx) = φ (AdjoinRoot.of q X)
      simp only [_root_.map_add, dx, _root_.map_neg, _root_.map_mul]
      change Ideal.Quotient.mk I x + -(Ideal.Quotient.mkₐ R I e * Ideal.Quotient.mk I av) = _
      rw [he0, zero_mul, neg_zero, add_zero, hx]
    · simp only [AlgHom.comp_apply, ψ, AdjoinRoot.liftAlgHom_root]
      change Ideal.Quotient.mk I (y + dy) = φ (AdjoinRoot.root q)
      simp only [_root_.map_add, dy, _root_.map_neg, _root_.map_mul]
      change Ideal.Quotient.mk I y + -(Ideal.Quotient.mkₐ R I e * Ideal.Quotient.mk I bv) = _
      rw [he0, zero_mul, neg_zero, add_zero, hy]
  exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

end MazurTransfer.MixedQuadraticCoordinateSmoothProof

theorem solution
    (R : Type*) [CommRing R] (h f : Polynomial R)
    (hjac : ∃ a b : AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)),
      a * (AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h.derivative *
        AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) -
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) f.derivative) +
      b * (2 * AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) +
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h) = 1) :
    Algebra.Smooth R (AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))) := by
  exact MazurTransfer.MixedQuadraticCoordinateSmoothProof.coordinate_smooth R h f hjac

#print axioms solution
