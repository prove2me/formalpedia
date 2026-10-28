-- Prove2me | solution 1 for NewtonCartan.riem_geomGamma
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:43:07.912029+00:00
-- url     : https://prove2.me/submissions/eb3ac79d-d828-4a34-b344-a5ccc7b31f6f

import Definitions.Def_NewtonCartan_defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! Malament (4.2.8): Riemann of Trautman geometrization. -/

private lemma gradUp_time (φ : E → ℝ) (x : E) : gradUp φ x 0 = 0 := by
  simp [gradUp, hh]

private lemma sum_tt_gradUp (φ : E → ℝ) (x : E) :
    (∑ n : Fin 4, tt n * gradUp φ x n) = 0 := by
  simp [tt, Finset.sum_ite_eq', gradUp_time]

private lemma sum_tt_Gamma (Γ : Conn) (hC : Compatible Γ) (x : E) (b c : Fin 4) :
    (∑ e : Fin 4, tt e * Γ x e b c) = 0 := by
  simpa [tt, Finset.sum_ite_eq', mul_comm] using hC.1 x b c

private lemma contDiff_pd (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (b : Fin 4) :
    ContDiff ℝ ∞ (fun x => pd φ b x) := by
  have hf := (contDiff_infty_iff_fderiv.1 hφ).2
  simpa [pd] using ContDiff.clm_apply hf contDiff_const

private lemma contDiff_gradUp_apply (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (a : Fin 4) :
    ContDiff ℝ ∞ (fun x => gradUp φ x a) := by
  simpa [gradUp] using
    ContDiff.sum (s := Finset.univ) (f := fun n : Fin 4 => fun x => hh a n * pd φ n x)
      (fun n _ => contDiff_const.mul (contDiff_pd φ hφ n))

private lemma diff_gradUp (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (a : Fin 4) :
    Differentiable ℝ (fun y => gradUp φ y a) :=
  (contDiff_gradUp_apply φ hφ a).differentiable (by simp)

private lemma diff_Gamma (Γ : Conn) (hΓ : ContDiff ℝ ∞ Γ) (a b c : Fin 4) :
    Differentiable ℝ (fun y => Γ y a b c) :=
  (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c).differentiable (by simp)

private lemma pd_geomΓ (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (a b c e : Fin 4) (x : E) :
    pd (fun y => geomΓ Γ φ y a b c) e x =
      pd (fun y => Γ y a b c) e x + tt b * tt c * pd (fun y => gradUp φ y a) e x := by
  have hΓ := diff_Gamma Γ hNG.1.1.1 a b c
  have hg := diff_gradUp φ hNG.2.2 a
  let f : E → ℝ := fun y => Γ y a b c
  let g : E → ℝ := fun y => (tt b * tt c) * gradUp φ y a
  have hf : DifferentiableAt ℝ f x := hΓ.differentiableAt
  have hg' : DifferentiableAt ℝ g x := (hg.const_mul (tt b * tt c)).differentiableAt
  have hsum : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x := fderiv_add hf hg'
  have hcmul : fderiv ℝ g x = (tt b * tt c) • fderiv ℝ (fun y => gradUp φ y a) x :=
    fderiv_const_mul (hg.differentiableAt) (tt b * tt c)
  simp only [geomΓ, pd, f, g] at *
  -- goal: (fderiv (Γ + c*grad)) (single e) = ...
  have hfun : (fun y => Γ y a b c + tt b * tt c * gradUp φ y a) = f + g := by
    funext y; simp [f, g, mul_assoc]
  rw [hfun, hsum, hcmul]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, mul_assoc]

private lemma geom_quad_expand (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (a b c d : Fin 4) :
    (∑ e : Fin 4,
        (geomΓ Γ φ x a d e * geomΓ Γ φ x e c b -
          geomΓ Γ φ x a c e * geomΓ Γ φ x e d b)) =
      (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) +
        tt b * (tt c * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
          tt d * (∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by
  have hC : Compatible Γ := hNG.1.2
  have hCG (p q : Fin 4) :
      (∑ e : Fin 4, (tt p * tt e * gradUp φ x a) * Γ x e q b) = 0 := by
    have hsum := sum_tt_Gamma Γ hC x q b
    have h :
        (∑ e : Fin 4, (tt p * tt e * gradUp φ x a) * Γ x e q b) =
          tt p * gradUp φ x a * (∑ e : Fin 4, tt e * Γ x e q b) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [h, hsum, mul_zero]
  have hCC :
      (∑ e : Fin 4,
        ((tt d * tt e * gradUp φ x a) * (tt c * tt b * gradUp φ x e) -
          (tt c * tt e * gradUp φ x a) * (tt d * tt b * gradUp φ x e))) = 0 := by
    have hg0 := sum_tt_gradUp φ x
    have h1 :
        (∑ e : Fin 4, (tt d * tt e * gradUp φ x a) * (tt c * tt b * gradUp φ x e)) =
          tt d * tt c * tt b * gradUp φ x a * (∑ e : Fin 4, tt e * gradUp φ x e) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have h2 :
        (∑ e : Fin 4, (tt c * tt e * gradUp φ x a) * (tt d * tt b * gradUp φ x e)) =
          tt c * tt d * tt b * gradUp φ x a * (∑ e : Fin 4, tt e * gradUp φ x e) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, h1, h2, hg0]; ring
  have hGC :
      (∑ e : Fin 4,
        (Γ x a d e * (tt c * tt b * gradUp φ x e) -
          Γ x a c e * (tt d * tt b * gradUp φ x e))) =
        tt b * (tt c * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
          tt d * (∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by
    simp only [Finset.sum_sub_distrib]
    have h1 :
        (∑ e : Fin 4, Γ x a d e * (tt c * tt b * gradUp φ x e)) =
          tt c * tt b * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have h2 :
        (∑ e : Fin 4, Γ x a c e * (tt d * tt b * gradUp φ x e)) =
          tt d * tt b * (∑ e : Fin 4, Γ x a c e * gradUp φ x e) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [h1, h2]; ring
  -- Expand (Γ+C)(Γ+C)
  simp only [geomΓ]
  have hexpand :
      (∑ e : Fin 4,
        ((Γ x a d e + tt d * tt e * gradUp φ x a) *
            (Γ x e c b + tt c * tt b * gradUp φ x e) -
          (Γ x a c e + tt c * tt e * gradUp φ x a) *
            (Γ x e d b + tt d * tt b * gradUp φ x e))) =
      (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) +
        (∑ e : Fin 4, (Γ x a d e * (tt c * tt b * gradUp φ x e) -
          Γ x a c e * (tt d * tt b * gradUp φ x e))) +
        (∑ e : Fin 4, ((tt d * tt e * gradUp φ x a) * Γ x e c b -
          (tt c * tt e * gradUp φ x a) * Γ x e d b)) +
        (∑ e : Fin 4, ((tt d * tt e * gradUp φ x a) * (tt c * tt b * gradUp φ x e) -
          (tt c * tt e * gradUp φ x a) * (tt d * tt b * gradUp φ x e))) := by
    -- Pointwise identity, then sum
    have hterm (e : Fin 4) :
        (Γ x a d e + tt d * tt e * gradUp φ x a) *
            (Γ x e c b + tt c * tt b * gradUp φ x e) -
          (Γ x a c e + tt c * tt e * gradUp φ x a) *
            (Γ x e d b + tt d * tt b * gradUp φ x e) =
        (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b) +
          (Γ x a d e * (tt c * tt b * gradUp φ x e) -
            Γ x a c e * (tt d * tt b * gradUp φ x e)) +
          ((tt d * tt e * gradUp φ x a) * Γ x e c b -
            (tt c * tt e * gradUp φ x a) * Γ x e d b) +
          ((tt d * tt e * gradUp φ x a) * (tt c * tt b * gradUp φ x e) -
            (tt c * tt e * gradUp φ x a) * (tt d * tt b * gradUp φ x e)) := by
      ring
    simp_rw [hterm, Finset.sum_add_distrib]
  -- CΓ as difference of two hCG applications
  have hCGdiff :
      (∑ e : Fin 4, ((tt d * tt e * gradUp φ x a) * Γ x e c b -
        (tt c * tt e * gradUp φ x a) * Γ x e d b)) = 0 := by
    rw [Finset.sum_sub_distrib, hCG d c, hCG c d]; ring
  rw [hexpand, hGC, hCGdiff, hCC]
  abel

theorem solution (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) (x : E) (a b c d : Fin 4) :
    riem (geomΓ Γ φ) x a b c d =
      tt b * (tt c * (pd (fun y => gradUp φ y a) d x +
          ∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
        tt d * (pd (fun y => gradUp φ y a) c x +
          ∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by
  have hflat : riem Γ x a b c d = 0 := hNG.2.1 x a b c d
  have hp1 := pd_geomΓ Γ φ hNG a c b d x
  have hp2 := pd_geomΓ Γ φ hNG a d b c x
  have hq := geom_quad_expand Γ φ hNG x a b c d
  -- riem geom = pd geom_cb d - pd geom_db c + quad
  simp only [riem]
  rw [hp1, hp2, hq]
  have hrw :
      pd (fun y => Γ y a c b) d x - pd (fun y => Γ y a d b) c x +
        (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) = 0 := by
    simpa [riem] using hflat
  calc
    pd (fun y => Γ y a c b) d x + tt c * tt b * pd (fun y => gradUp φ y a) d x -
          (pd (fun y => Γ y a d b) c x + tt d * tt b * pd (fun y => gradUp φ y a) c x) +
        ((∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) +
          tt b * (tt c * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
            tt d * (∑ e : Fin 4, Γ x a c e * gradUp φ x e))) =
      (pd (fun y => Γ y a c b) d x - pd (fun y => Γ y a d b) c x +
          (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b))) +
        (tt c * tt b * pd (fun y => gradUp φ y a) d x -
          tt d * tt b * pd (fun y => gradUp φ y a) c x) +
        tt b * (tt c * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
          tt d * (∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by abel
    _ = 0 + (tt c * tt b * pd (fun y => gradUp φ y a) d x -
          tt d * tt b * pd (fun y => gradUp φ y a) c x) +
        tt b * (tt c * (∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
          tt d * (∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by rw [hrw]
    _ = tt b * (tt c * (pd (fun y => gradUp φ y a) d x +
          ∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
        tt d * (pd (fun y => gradUp φ y a) c x +
          ∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by ring
