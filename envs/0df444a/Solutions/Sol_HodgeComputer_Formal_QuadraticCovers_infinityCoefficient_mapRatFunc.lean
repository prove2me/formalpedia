-- Prove2me | solution 1 for HodgeComputer.Formal.QuadraticCovers.infinityCoefficient_mapRatFunc
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:35:51.652711+00:00
-- url     : https://prove2.me/submissions/97d38e83-19af-4903-a7d9-8c6c4ca75feb

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_residue_mapRatFunc
import Mathlib.Tactic

set_option autoImplicit false
open CrossedRationalResidue QuadraticCovers Polynomial

private lemma mapRatFunc_reciprocal {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    mapRatFunc f (reciprocal g) = reciprocal (mapRatFunc f g) := by
  have hpoly (R : K[X]) :
      mapRatFunc f (reciprocal (algebraMap K[X] (RatFunc K) R)) =
        reciprocal (mapRatFunc f (algebraMap K[X] (RatFunc K) R)) := by
    induction R using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        reciprocal_C, reciprocal_X, mapRatFunc_C, mapRatFunc_X, map_inv₀]
  induction g using RatFunc.induction_on with
  | f P Q _ =>
    simp only [map_div₀, hpoly]


theorem solution
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    CrossedRationalResidue.infinityCoefficient (QuadraticCovers.mapRatFunc f g) =
      f (CrossedRationalResidue.infinityCoefficient g) := by
  change residue 0 ((RatFunc.X ^ 2)⁻¹ * reciprocal (mapRatFunc f g)) =
    f (residue 0 ((RatFunc.X ^ 2)⁻¹ * reciprocal g))
  rw [← mapRatFunc_reciprocal, ← map_zero f, ← HodgeComputer.Formal.QuadraticCovers.residue_mapRatFunc]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, mapRatFunc_X]
