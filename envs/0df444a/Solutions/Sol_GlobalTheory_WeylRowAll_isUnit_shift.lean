-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.isUnit_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:06.979348+00:00
-- url     : https://prove2.me/submissions/12604973-b061-48c9-99fe-810ab3d6998d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll
namespace GlobalTheory.WeylRowAll
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    IsUnit ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) := by
  set A : Matrix (Fin r) (Fin r) (PowerSeries R) :=
    1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA
  have h1 : IsUnit A.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (PowerSeries.constantCoeff (R := R)).mapMatrix A = 1 := by
      ext i j
      by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]
    rw [this]; simp
  have h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det := by
    have := h1.map (HahnSeries.ofPowerSeries ℤ R)
    rwa [RingHom.map_det] at this
  have hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  have h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R) := by
    refine Matrix.ext fun i j => ?_
    simp only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT,
      one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Matrix.one_apply]
    rw [add_comm]
    split_ifs <;> simp
  rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hT).pow _).mul h2
end GlobalTheory.WeylRowAll
