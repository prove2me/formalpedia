-- Prove2me | solution 1 for NewtonCartan.geom_naturality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:52:51.059048+00:00
-- url     : https://prove2.me/submissions/dde6e5d5-64b1-4c39-b358-6bff2162c351

import Definitions.Def_NewtonCartan_defs
import Mathlib
open scoped ContDiff
open NewtonCartan

theorem g69h2_chain (f : E ≃ E) (hf : ContDiff ℝ ∞ f) (φ φ' : E → ℝ) (hφ' : ContDiff ℝ ∞ φ')
    (hpush : ∀ x, φ' (f x) = φ x) (n : Fin 4) (x : E) :
    pd φ n x = ∑ m, pd φ' m (f x) * pd (fun y => f y m) n x := by
  have hφeq : φ = φ' ∘ f := funext fun x => (hpush x).symm
  have hdf : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have hdφ : DifferentiableAt ℝ φ' (f x) := hφ'.differentiable (by simp) (f x)
  have hcomp : fderiv ℝ φ x = (fderiv ℝ φ' (f x)).comp (fderiv ℝ f x) := by
    rw [hφeq]; exact fderiv_comp x hdφ hdf
  have hcoord : ∀ m, fderiv ℝ (fun y => f y m) x =
      (ContinuousLinearMap.proj m : E →L[ℝ] ℝ).comp (fderiv ℝ f x) := by
    intro m
    have : (fun y => f y m) = (ContinuousLinearMap.proj m : E →L[ℝ] ℝ) ∘ f := rfl
    rw [this, fderiv_comp x (ContinuousLinearMap.proj m).differentiableAt hdf,
      ContinuousLinearMap.fderiv]
  unfold pd
  rw [hcomp]
  simp only [hcoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  set w := fderiv ℝ f x (Pi.single n 1)
  have hw : w = ∑ m, w m • (Pi.single m (1:ℝ) : E) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem solution (Γ Γ' : Conn) (φ φ' : E → ℝ) (f : E ≃ E) (hf : IsDiffeo f)
    (hm : PreservesMetrics f) (hφ : ContDiff ℝ ∞ φ) (hφ' : ContDiff ℝ ∞ φ')
    (hpush : ∀ x, φ' (f x) = φ x) :
    MapsConn f Γ Γ' ↔ MapsConn f (geomΓ Γ φ) (geomΓ Γ' φ') := by
  -- notation
  have key : ∀ x a b c,
      (∑ d, ∑ e, geomΓ Γ' φ' (f x) a d e * pd (fun y => f y d) b x * pd (fun y => f y e) c x
        = ∑ d, ∑ e, Γ' (f x) a d e * pd (fun y => f y d) b x * pd (fun y => f y e) c x
          + tt b * tt c * gradUp φ' (f x) a) ∧
      (∑ n, pd (fun y => f y a) n x * geomΓ Γ φ x n b c
        = ∑ n, pd (fun y => f y a) n x * Γ x n b c + tt b * tt c * gradUp φ' (f x) a) := by
    intro x a b c
    constructor
    · simp only [geomΓ, add_mul, Finset.sum_add_distrib]
      congr 1
      have h1 := hm.1 x b
      have h2 := hm.1 x c
      calc ∑ d, ∑ e, tt d * tt e * gradUp φ' (f x) a * pd (fun y => f y d) b x *
            pd (fun y => f y e) c x
          = gradUp φ' (f x) a * ((∑ d, tt d * pd (fun y => f y d) b x) *
              (∑ e, tt e * pd (fun y => f y e) c x)) := by
            rw [Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            ring
        _ = tt b * tt c * gradUp φ' (f x) a := by rw [h1, h2]; ring
    · simp only [geomΓ, mul_add, Finset.sum_add_distrib]
      congr 1
      have hg : ∀ n, gradUp φ x n =
          ∑ k, hh n k * ∑ m, pd φ' m (f x) * pd (fun y => f y m) k x := by
        intro n; unfold gradUp
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [g69h2_chain f hf.1 φ φ' hφ' hpush k x]
      have : ∑ n, pd (fun y => f y a) n x * gradUp φ x n = gradUp φ' (f x) a := by
        simp only [hg]
        unfold gradUp
        calc ∑ n, pd (fun y => f y a) n x *
              ∑ k, hh n k * ∑ m, pd φ' m (f x) * pd (fun y => f y m) k x
            = ∑ m, pd φ' m (f x) * ∑ n, ∑ k,
                pd (fun y => f y a) n x * pd (fun y => f y m) k x * hh n k := by
              simp only [Finset.mul_sum]
              refine (Finset.sum_congr rfl fun n _ => Finset.sum_comm).trans ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun m _ => ?_
              refine Finset.sum_congr rfl fun n _ => ?_
              refine Finset.sum_congr rfl fun k _ => ?_
              ring
          _ = ∑ m, hh a m * pd φ' m (f x) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [hm.2 x a m]; ring
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
  constructor
  · intro h x a b c
    rw [(key x a b c).1, (key x a b c).2, ← h x a b c]; ring
  · intro h x a b c
    have := h x a b c
    rw [(key x a b c).1, (key x a b c).2] at this
    linarith
