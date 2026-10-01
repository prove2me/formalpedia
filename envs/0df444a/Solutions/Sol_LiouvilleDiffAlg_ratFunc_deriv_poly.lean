-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_deriv_poly
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:42:59.512464+00:00
-- url     : https://prove2.me/submissions/4c027754-d160-435c-8b73-ad2db59c4aae

import Mathlib

open scoped Differential
open Polynomial

theorem solution {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (w : K[X]) (hX : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) w) (r : K[X]) :
    (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) (Differential.implicitDeriv w r) := by
  have h := Differential.deriv_aeval_eq_implicitDeriv (A := K) (R := RatFunc K) (RatFunc.X : RatFunc K) w
    (by rw [RatFunc.aeval_X_left_eq_algebraMap]; exact hX) r
  rwa [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap] at h
