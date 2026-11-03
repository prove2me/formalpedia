-- Prove2me | solution 1 for HeteroBass.HetP.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:25:04.340791+00:00
-- url     : https://prove2.me/submissions/944df680-2795-4c49-8790-0facf97049b1

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

open HeteroBass.HetP

namespace HBL4M

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma entry_hasDerivAt {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (i j : α) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) i j)
      (∑ k, NormedSpace.exp (t • A) i k * A k j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  have hc : HasDerivAt (fun u : ℝ => (NormedSpace.exp (u • A)) i j)
      ((NormedSpace.exp (t • A) * A) i j) t := by
    have := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => α → ℝ) i))).hasFDerivAt.comp_hasDerivAt t h
    exact this
  simpa [Matrix.mul_apply] using hc

lemma c_e : (∅ : Finset (Fin 2))ᶜ = {0, 1} := by decide
lemma c_0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
lemma c_1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
lemma c_01 : ({0, 1} : Finset (Fin 2))ᶜ = ∅ := by decide
lemma univ_fs2 : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

variable (p : Fin 2 → ℝ) (q : ℝ)


lemma x_deriv (S : Finset (Fin 2)) (t : ℝ) :
    HasDerivAt (fun u => (transition p (completeQ (fun _ : Fin 2 => q)) u ∅) S)
      (∑ k, (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) k * generator p (completeQ (fun _ : Fin 2 => q)) k S) t :=
  entry_hasDerivAt _ _ _ t

lemma x_init (S : Finset (Fin 2)) : (transition p (completeQ (fun _ : Fin 2 => q)) 0 ∅) S = if S = ∅ then 1 else 0 := by
  simp only [transition, zero_smul, NormedSpace.exp_zero]
  rw [Matrix.one_apply]
  by_cases h : S = ∅ <;> simp [h, eq_comm]

lemma d_e (t : ℝ) : HasDerivAt (fun u => (transition p (completeQ (fun _ : Fin 2 => q)) u ∅) ∅) (-(p 0 + p 1) * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) ∅) t := by
  refine (x_deriv p q ∅ t).congr_deriv ?_
  simp (config := {decide := true}) [generator, finiteJumpGenerator, adopterJumpRate, adoptRate,
    completeQ, univ_fs2, c_e, c_0, c_1, c_01, Finset.sum_insert, Finset.sum_pair]
  ring

lemma d_0 (t : ℝ) : HasDerivAt (fun u => (transition p (completeQ (fun _ : Fin 2 => q)) u ∅) {0})
    (p 0 * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) ∅ - (p 1 + q) * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {0}) t := by
  refine (x_deriv p q {0} t).congr_deriv ?_
  simp (config := {decide := true}) [generator, finiteJumpGenerator, adopterJumpRate, adoptRate,
    completeQ, univ_fs2, c_e, c_0, c_1, c_01, Finset.sum_insert, Finset.sum_pair]
  ring

lemma d_1 (t : ℝ) : HasDerivAt (fun u => (transition p (completeQ (fun _ : Fin 2 => q)) u ∅) {1})
    (p 1 * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) ∅ - (p 0 + q) * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {1}) t := by
  refine (x_deriv p q {1} t).congr_deriv ?_
  simp (config := {decide := true}) [generator, finiteJumpGenerator, adopterJumpRate, adoptRate,
    completeQ, univ_fs2, c_e, c_0, c_1, c_01, Finset.sum_insert, Finset.sum_pair]
  ring

lemma d_01 (t : ℝ) : HasDerivAt (fun u => (transition p (completeQ (fun _ : Fin 2 => q)) u ∅) {0, 1})
    ((p 1 + q) * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {0} + (p 0 + q) * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {1}) t := by
  refine (x_deriv p q {0, 1} t).congr_deriv ?_
  simp (config := {decide := true}) [generator, finiteJumpGenerator, adopterJumpRate, adoptRate,
    completeQ, univ_fs2, c_e, c_0, c_1, c_01, Finset.sum_insert, Finset.sum_pair]
  ring

lemma ef_eq (t : ℝ) : expectedFraction p (completeQ (fun _ : Fin 2 => q)) t =
    ((transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {0} + (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {1} + 2 * (transition p (completeQ (fun _ : Fin 2 => q)) t ∅) {0, 1}) / 2 := by
  simp (config := {decide := true}) [expectedFraction, univ_fs2, Finset.sum_insert, Finset.sum_pair]
  ring



lemma ifac {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t) :
    ∀ t, HasDerivAt (fun s => Real.exp (K * s) * y s) (Real.exp (K * t) * g t) t := by
  intro t
  have h1 : HasDerivAt (fun s => Real.exp (K * s)) (Real.exp (K * t) * K) t := by
    have := ((hasDerivAt_id t).const_mul K).exp
    simpa [mul_comm] using this
  exact (h1.mul (hy t)).congr_deriv (by ring)

lemma IF_pos {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t)
    (h0 : y 0 = 0) (hg : ∀ t, 0 < t → 0 < g t) : ∀ t, 0 < t → 0 < y t := by
  have hφ := ifac K hy
  have hmono : StrictMonoOn (fun s => Real.exp (K * s) * y s) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro t _; exact (hφ t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφ t).deriv]
      exact mul_pos (Real.exp_pos _) (hg t ht)
  intro t ht
  have := hmono ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr ht.le) ht
  simp only [mul_zero, h0] at this
  exact pos_of_mul_pos_right this (Real.exp_pos _).le

lemma IF_nonneg {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t)
    (h0 : y 0 = 0) (hg : ∀ t, 0 < t → 0 ≤ g t) : ∀ t, 0 ≤ t → 0 ≤ y t := by
  have hφ := ifac K hy
  have hmono : MonotoneOn (fun s => Real.exp (K * s) * y s) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t _; exact (hφ t).continuousAt.continuousWithinAt
    · intro t _; exact (hφ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφ t).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hg t ht)
  intro t ht
  have := hmono ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr ht) ht
  simp only [mul_zero, h0] at this
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using this) (Real.exp_pos _)

lemma const_of_deriv {y : ℝ → ℝ} (hy : ∀ t, HasDerivAt y 0 t) : ∀ t, y t = y 0 := by
  intro t
  exact is_const_of_deriv_eq_zero (fun s => (hy s).differentiableAt) (fun s => (hy s).deriv) t 0

lemma exp_sol {a : ℝ → ℝ} (s : ℝ) (ha : ∀ t, HasDerivAt a (-s * a t) t) (h0 : a 0 = 1) :
    ∀ t, a t = Real.exp (-s * t) := by
  have hφ := ifac s (g := fun _ => 0) (by intro t; simpa using ha t)
  have hc := const_of_deriv (y := fun u => Real.exp (s * u) * a u) (by intro t; simpa using hφ t)
  intro t
  have := hc t
  simp only [mul_zero, Real.exp_zero, h0, one_mul] at this
  have he : Real.exp (-s * t) * Real.exp (s * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc a t = Real.exp (-s * t) * (Real.exp (s * t) * a t) := by rw [← mul_assoc, he, one_mul]
    _ = Real.exp (-s * t) := by rw [this, mul_one]

/-- The abstract ODE comparison behind Lemma 4. -/
lemma core (p0 p1 q : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hne : p0 ≠ p1)
    (a b d e ah bh dh eh : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a (-(p0 + p1) * a t) t)
    (hb : ∀ t, HasDerivAt b (p0 * a t - (p1 + q) * b t) t)
    (hd : ∀ t, HasDerivAt d (p1 * a t - (p0 + q) * d t) t)
    (he : ∀ t, HasDerivAt e ((p1 + q) * b t + (p0 + q) * d t) t)
    (hah : ∀ t, HasDerivAt ah (-((p0 + p1) / 2 + (p0 + p1) / 2) * ah t) t)
    (hbh : ∀ t, HasDerivAt bh ((p0 + p1) / 2 * ah t - ((p0 + p1) / 2 + q) * bh t) t)
    (hdh : ∀ t, HasDerivAt dh ((p0 + p1) / 2 * ah t - ((p0 + p1) / 2 + q) * dh t) t)
    (heh : ∀ t, HasDerivAt eh (((p0 + p1) / 2 + q) * bh t + ((p0 + p1) / 2 + q) * dh t) t)
    (a0 : a 0 = 1) (b0 : b 0 = 0) (d0 : d 0 = 0) (e0 : e 0 = 0)
    (ah0 : ah 0 = 1) (bh0 : bh 0 = 0) (dh0 : dh 0 = 0) (eh0 : eh 0 = 0) :
    ∀ t, 0 < t → (b t + d t + 2 * e t) / 2 < (bh t + dh t + 2 * eh t) / 2 := by
  set P := (p0 + p1) / 2 with hP
  set δ := (p0 - p1) / 2 with hδ
  have hδ0 : δ ≠ 0 := by
    intro h; apply hne; linarith [show p0 - p1 = 0 by linarith]
  have aeq := exp_sol _ ha a0
  have aheq := exp_sol _ hah ah0
  have hsame : ∀ t, ah t = a t := by
    intro t; rw [aeq, aheq]; congr 1; ring
  have apos : ∀ t, 0 < a t := fun t => by rw [aeq]; exact Real.exp_pos _
  -- nonnegativity of b and d
  have bnn := IF_nonneg (p1 + q) (g := fun t => p0 * a t)
    (by intro t; convert hb t using 1; ring) b0 (fun t _ => mul_nonneg hp0 (apos t).le)
  have dnn := IF_nonneg (p0 + q) (g := fun t => p1 * a t)
    (by intro t; convert hd t using 1; ring) d0 (fun t _ => mul_nonneg hp1 (apos t).le)
  -- δ w
  have hw : ∀ t, HasDerivAt (fun s => δ * (b s - d s))
      (-(P + q) * (δ * (b t - d t)) + δ ^ 2 * (2 * a t + (b t + d t))) t := by
    intro t
    exact (((hb t).sub (hd t)).const_mul δ).congr_deriv (by rw [hP, hδ]; ring)
  have wpos := IF_pos (P + q) hw (by simp [b0, d0])
    (fun t ht => mul_pos (by positivity)
      (by have := apos t; have := bnn t ht.le; have := dnn t ht.le; linarith))
  -- σ = (b + d) - (bh + dh)
  have hσ : ∀ t, HasDerivAt (fun s => (b s + d s) - (bh s + dh s))
      (-(P + q) * ((b t + d t) - (bh t + dh t)) + δ * (b t - d t)) t := by
    intro t
    exact (((hb t).add (hd t)).sub ((hbh t).add (hdh t))).congr_deriv
      (by rw [hsame t, hP, hδ]; ring)
  have σpos := IF_pos (P + q) hσ (by simp [b0, d0, bh0, dh0]) wpos
  -- D - σ/2 is constant
  have hD : ∀ t, HasDerivAt (fun s => ((bh s + dh s + 2 * eh s) / 2 - (b s + d s + 2 * e s) / 2)
      - ((b s + d s) - (bh s + dh s)) / 2) 0 t := by
    intro t
    have := ((((((hbh t).add (hdh t)).add ((heh t).const_mul 2)).div_const 2).sub
      ((((hb t).add (hd t)).add ((he t).const_mul 2)).div_const 2)).sub
      ((((hb t).add (hd t)).sub ((hbh t).add (hdh t))).div_const 2))
    exact this.congr_deriv (by rw [hsame t, hP]; ring)
  intro t ht
  have h1 := const_of_deriv hD t
  simp only [b0, d0, e0, bh0, dh0, eh0] at h1
  have := σpos t ht
  linarith


end HBL4M

open HBL4M in
theorem solution (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hhetero : p 0 ≠ p 1) (q : ℝ) (hq : 0 < q)
    (t : ℝ) (ht : 0 < t) :
    expectedFraction p (completeQ (fun _ : Fin 2 => q)) t <
      expectedFraction (fun _ : Fin 2 => (p 0 + p 1) / 2)
        (completeQ (fun _ : Fin 2 => q)) t := by
  rw [ef_eq, ef_eq]
  set ph : Fin 2 → ℝ := fun _ => (p 0 + p 1) / 2
  have i_e := x_init p q ∅
  have i_0 := x_init p q {0}
  have i_1 := x_init p q {1}
  have i_01 := x_init p q {0, 1}
  have j_e := x_init ph q ∅
  have j_0 := x_init ph q {0}
  have j_1 := x_init ph q {1}
  have j_01 := x_init ph q {0, 1}
  simp (config := {decide := true}) only [if_true, if_false, Finset.singleton_ne_empty,
    Finset.insert_ne_empty] at i_e i_0 i_1 i_01 j_e j_0 j_1 j_01
  exact core (p 0) (p 1) q (hp 0) (hp 1) hhetero _ _ _ _ _ _ _ _
    (d_e p q) (d_0 p q) (d_1 p q) (d_01 p q) (d_e ph q) (d_0 ph q) (d_1 ph q) (d_01 ph q)
    i_e i_0 i_1 i_01 j_e j_0 j_1 j_01 t ht
