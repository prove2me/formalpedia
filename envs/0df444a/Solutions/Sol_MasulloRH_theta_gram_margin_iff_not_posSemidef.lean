-- Prove2me | solution 1 for MasulloRH.theta_gram_margin_iff_not_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:52:09.651361+00:00
-- url     : https://prove2.me/submissions/51cfc999-29b3-42ac-be8b-19e6d84a10b7

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MasulloRH.GaussianApproximation MeasureTheory
open scoped ComplexConjugate
open Matrix
open scoped BigOperators Matrix

private noncomputable def quad {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * A i j

private theorem dot_eq_quad {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    star v ⬝ᵥ (A *ᵥ v) = quad A v := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, quad]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quad_shift {m : ℕ} (G : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (τ : ℝ) (v : Fin (m+1) → ℝ) :
    quad (G - Matrix.single 0 0 τ) v = quad G v - v 0^2 * τ := by
  have hs : quad (Matrix.single 0 0 τ) v = v 0^2 * τ := by
    have hzero (i : Fin m) : (0 : Fin (m+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp [quad, Fin.sum_univ_succ, Matrix.single_apply, pow_two, hzero]
  rw [← hs]
  simp only [quad, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem quad_scale {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (c : ℝ) (v : Fin k → ℝ) :
    quad A (fun i => c * v i) = c^2 * quad A v := by
  simp only [quad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem real_margin (m : ℕ) (G : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hG : G.IsHermitian) (τ : ℝ) :
    ¬ (G - Matrix.single 0 0 τ).PosSemidef ↔
      ∃ a : Fin m → ℚ, let v : Fin (m+1) → ℝ := Fin.cons 1 (fun i => (a i : ℝ))
        (∑ i, ∑ j, v i * v j * G i j) < τ := by
  classical
  let H := G - Matrix.single 0 0 τ
  have hs : (Matrix.single (0 : Fin (m+1)) 0 τ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.single_apply, and_comm]
  have hH : H.IsHermitian := hG.sub hs
  constructor
  · intro h
    have hex : ∃ v : Fin (m+1) → ℝ, quad H v < 0 := by
      by_contra! hn
      exact h (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun v => (dot_eq_quad H v) ▸ hn v))
    have hc : Continuous (quad H) := by unfold quad; fun_prop
    have hrat : DenseRange (fun q : {r : ℚ // r ≠ 0} => (q.val : ℝ)) := by
      have hden : DenseRange (fun q : {r : ℚ // r ≠ 0} => q.val) :=
        denseRange_subtype_val.mpr (dense_compl_singleton (0 : ℚ))
      exact (Rat.denseRange_cast (𝕜 := ℝ)).comp hden Rat.continuous_coe_real
    have hdense : DenseRange (fun r : Fin (m+1) → {s : ℚ // s ≠ 0} =>
        fun i => ((r i).val : ℝ)) := DenseRange.piMap (fun _ => hrat)
    obtain ⟨r, hr⟩ :=
      hdense.exists_mem_open (isOpen_lt hc continuous_const) hex
    let x (i : Fin (m+1)) : ℝ := (r i).val
    change quad H x < 0 at hr
    have hx : x 0 ≠ 0 := by
      dsimp [x]
      exact_mod_cast (r 0).property
    let a (i : Fin m) : ℚ := (r i.succ).val / (r 0).val
    let v : Fin (m+1) → ℝ := Fin.cons 1 (fun i => (a i : ℝ))
    have hnorm : v = fun i => (x 0)⁻¹ * x i := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [v, hx]
      · simp [v, a, x, div_eq_mul_inv, mul_comm]
    have hv : quad H v < 0 := by
      rw [hnorm, quad_scale]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (inv_ne_zero hx)) hr
    change quad (G - Matrix.single 0 0 τ) v < 0 at hv
    rw [quad_shift] at hv
    have hv0 : v 0 = 1 := rfl
    rw [hv0, one_pow, one_mul] at hv
    exact ⟨a, sub_neg.mp hv⟩
  · rintro ⟨a, ha⟩ hpos
    let v : Fin (m+1) → ℝ := Fin.cons 1 (fun i => (a i : ℝ))
    change quad G v < τ at ha
    have h := hpos.dotProduct_mulVec_nonneg v
    rw [dot_eq_quad, quad_shift] at h
    have hv0 : v 0 = 1 := rfl
    rw [hv0, one_pow, one_mul] at h
    linarith


theorem solution (n m : ℕ) (y : Fin m → ℚ) :
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    (∃ a : Fin m → ℚ × ℚ,
      let d : Fin (m+1) → ℂ := Fin.cons 1 (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
      (∑ i, ∑ j, conj (d i) * d j * G i j).re < δ / 2) ↔ ¬ (K - Matrix.single 0 0 (δ / 2)).PosSemidef := by
  classical
  let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
  let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
  let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
    ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
  let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
  let coeff (a : Fin m → ℚ × ℚ) : Fin (m+1) → ℂ := Fin.cons 1
    (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I))
  change (∃ a, (∑ i, ∑ j, conj (coeff a i) * coeff a j * G i j).re < δ/2) ↔
    ¬ (K - Matrix.single 0 0 (δ/2)).PosSemidef
  have hu (i : Fin (m+1)) (x : ℝ) : conj (u i x) = u i x := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change conj (pulse (n : ℝ) x) = _
      simp [u, pulse, ← Complex.exp_conj]
    · change conj (theta (x - (y j : ℝ))) = theta (x - (y j : ℝ))
      simp only [theta, Complex.conj_tsum, Complex.conj_ofReal]
  have hreal (i j : Fin (m+1)) : (G i j).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    dsimp only [G]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [map_mul, Complex.conj_ofReal, hu]
  have hsym : K.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply congrArg Complex.re
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hu, hu]
    ring
  have hdecomp (v : Fin (m+1) → ℂ) :
      (∑ i, ∑ j, conj (v i) * v j * G i j).re =
        quad K (fun i => (v i).re) + quad K (fun i => (v i).im) := by
    simp only [quad, Complex.re_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [K, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hreal]
    ring
  constructor
  · rintro ⟨a, ha⟩ hpos
    have hb (v : Fin (m+1) → ℝ) : 0 ≤ quad K v - v 0^2 * (δ/2) := by
      have h := hpos.dotProduct_mulVec_nonneg v
      rwa [dot_eq_quad, quad_shift] at h
    let v := coeff a
    have hre := hb (fun i => (v i).re)
    have him := hb (fun i => (v i).im)
    have h0 : v 0 = 1 := rfl
    change (∑ i, ∑ j, conj (v i) * v j * G i j).re < δ/2 at ha
    rw [hdecomp] at ha
    simp only [h0, Complex.one_re, Complex.one_im, one_pow, one_mul, zero_pow (by decide : 2 ≠ 0),
      zero_mul, sub_zero] at hre him
    linarith
  · intro h
    obtain ⟨a, ha⟩ := (real_margin m K hsym (δ/2)).mp h
    let b (i : Fin m) : ℚ × ℚ := (-a i, 0)
    let v : Fin (m+1) → ℝ := Fin.cons 1 (fun i => (a i : ℝ))
    have hb (i : Fin (m+1)) : coeff b i = (v i : ℂ) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [coeff, v]
      · simp [coeff, b, v]
    refine ⟨b, ?_⟩
    rw [hdecomp]
    simpa only [hb, Complex.ofReal_re, Complex.ofReal_im, quad, zero_mul, Finset.sum_const_zero,
      add_zero] using ha
