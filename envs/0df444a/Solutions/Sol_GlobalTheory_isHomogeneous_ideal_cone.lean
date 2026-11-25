-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_ideal_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:31.920554+00:00
-- url     : https://prove2.me/submissions/7f9b0ea0-a9f9-4293-b1fd-488a072fc5d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
private theorem eval_smul_of_isHomogeneous_toric_geometry {σ : Type} {P : MvPolynomial σ ℂ} {n : ℕ}
    (hP : P.IsHomogeneous n) (t : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun c => t * x c) P = t ^ n * MvPolynomial.eval x P := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {σ E : Type} [Fintype σ] (f : σ → E → ℂ) (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0) :
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℂ) := by
  intro i F hF
  have hdec : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ ℂ) F i : MvPolynomial σ ℂ) =
      MvPolynomial.homogeneousComponent i F := MvPolynomial.decomposition.decompose'_apply F i
  rw [hdec, hI]
  intro t z
  rw [eval_smul_of_isHomogeneous_toric_geometry (MvPolynomial.homogeneousComponent_isHomogeneous i F)]
  suffices h0 : MvPolynomial.eval (fun c => f c z) (MvPolynomial.homogeneousComponent i F) = 0 by
    simp [h0]
  let Q : Polynomial ℂ := ∑ n ∈ Finset.range (F.totalDegree + 1),
    Polynomial.C (MvPolynomial.eval (fun c => f c z) (MvPolynomial.homogeneousComponent n F)) *
      Polynomial.X ^ n
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    have hs := (hI F).1 hF s z
    conv_lhs at hs => rw [← MvPolynomial.sum_homogeneousComponent F]
    rw [map_sum] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eval_smul_of_isHomogeneous_toric_geometry (MvPolynomial.homogeneousComponent_isHomogeneous n F)]
    ring
  by_cases hi : i ≤ F.totalDegree
  · have hc := congrArg (fun P => Polynomial.coeff P i) hQ
    simpa [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.mem_range,
      Nat.lt_succ_iff.mpr hi] using hc
  · rw [MvPolynomial.homogeneousComponent_eq_zero, map_zero]
    omega
end GlobalTheory
