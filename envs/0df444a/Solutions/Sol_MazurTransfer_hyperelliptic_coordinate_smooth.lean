-- Prove2me | solution 1 for MazurTransfer.hyperelliptic_coordinate_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T20:44:28.906391+00:00
-- url     : https://prove2.me/submissions/46318b97-3712-4843-b5a2-14ed2787ffee

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine smoothness of a quadratic hyperelliptic coordinate
algebra over a field of characteristic different from two. Named downstream consumer: smoothness of
MazurTorsion.XOneThirteenAffineCurve.scheme and the two-chart curve.
The polynomial separability hypothesis is explicit and separately checked
for the actual order-thirteen sextic.
-/
import Mathlib

noncomputable section
open Polynomial

theorem solution (K : Type*) [Field K] (f : Polynomial K)
    (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (AdjoinRoot
      ((Polynomial.X ^ 2 - Polynomial.C f) : Polynomial (Polynomial K))) := by
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

