-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:15:45.030466+00:00
-- url     : https://prove2.me/submissions/43a299de-05e1-42fa-95ca-0720b3be6d35

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero unweighted lattice Gaussian, with its exact ideal multiplicity
and exponential decay. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

lemma cubicThetaLatticeGaussianTail_summable {t : ℝ} (ht : 0<t) :
    Summable (fun a : {a : Eisenstein // a≠0} => Real.exp (-t*norm a.val)) := by
  have h := (principalLatticeTheta_summable
    (mul_pos ht (residueHeckeScale_pos (q:=1) one_ne_zero))).subtype
    (fun a : Eisenstein => a≠0)
  have hA := (residueHeckeScale_pos (q:=1) one_ne_zero).ne'
  convert h.norm using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  dsimp only [Function.comp_apply]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  congr 1
  field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianPowerBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global quadratic decay bound for the nonzero Gaussian lattice tail. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGaussianPowerConstant_nonneg : 0 ≤ cubicThetaGaussianPowerConstant := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))

lemma cubicThetaLatticeGaussianTail_power_bound {t : ℝ} (ht : 0<t) :
    cubicThetaLatticeGaussianTail t ≤ cubicThetaGaussianPowerConstant/t^2 := by
  have hs : Summable (fun a : {a : Eisenstein // a≠0} => (norm a.val)^(-2:ℝ)) := by
    have h := (summable_eisenstein_norm_rpow (s:=2) (by norm_num)).subtype
      (fun a : Eisenstein => a≠0)
    exact h
  have hm := hs.mul_left (2/t^2)
  have he : ∀ a : {a : Eisenstein // a≠0},
      Real.exp (-t*norm a.val)≤(2/t^2)*(norm a.val)^(-2:ℝ) := by
    intro a
    have hn := norm_pos_of_ne_zero a.property
    have h := power_exp_bound ht 2 (norm a.val) hn.le
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
      Nat.cast_ofNat,mul_one] at h
    rw [Real.rpow_neg hn.le,Real.rpow_ofNat,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith [h]
  have h := (cubicThetaLatticeGaussianTail_summable ht).tsum_le_tsum he hm
  rw [tsum_mul_left] at h
  exact h.trans_eq (by unfold cubicThetaGaussianPowerConstant; ring)

lemma cubicThetaLatticeGaussianTail_div_bound {c t : ℝ} (hc : 0 < c) (ht : 0<t) :
    cubicThetaLatticeGaussianTail (c/t)≤(cubicThetaGaussianPowerConstant/c^2)*t^2 := by
  apply (cubicThetaLatticeGaussianTail_power_bound (div_pos hc ht)).trans_eq
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unweighted Gaussian on the affine level-three lattice. This is the
scalar Poisson kernel used to compute the height-series residue. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

lemma cubicThetaScalarGaussian_summable (z : ℂ) {t : ℝ} (ht : 0<t) :
    Summable (fun a : Eisenstein =>
      (Real.exp (-t*Complex.normSq (z+3*(a:ℂ))):ℂ)) := by
  let F := cubicThetaShiftedGaussian (1/3) z (by norm_num) t ht
  have h := schwartz_summable_eisenstein F
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  dsimp only [F]
  rw [cubicThetaShiftedGaussian_apply,Complex.normSq_eq_norm_sq]
  rw [show (a:ℂ)/(1/3)=3*(a:ℂ) by ring]

theorem cubicThetaScalarGaussian_poisson (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussian z t=(2*Real.pi/(9*Real.sqrt 3*t):ℝ)*
      ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
          (Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ) := by
  have hp := poisson_eisenstein_coset (radialGaussianSchwartz t ht)
    (3:ℂ) (by norm_num) z
  simp_rw [radialGaussianSchwartz_apply,radialGaussianSchwartz_traceFourier] at hp
  have he (h : Eisenstein) :
      -4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))=
        -(4*Real.pi^2/(27*t))*norm h := by
    rw [Complex.normSq_div,Complex.normSq_mul,traceLambda_normSq]
    rw [show Complex.normSq (3:ℂ)=9 by norm_num [Complex.normSq_apply]]
    change -4*Real.pi^2/t*(norm h/(9*3))=_
    ring
  simp_rw [he] at hp
  rw [show Complex.normSq (3:ℂ)=9 by norm_num [Complex.normSq_apply]] at hp
  simp only [Complex.real_smul] at hp
  rw [show cubicThetaScalarGaussian z t=
      ∑' a : Eisenstein,(Real.exp (-t*‖z+3*(a:ℂ)‖^2):ℂ) by
    simp only [cubicThetaScalarGaussian,Complex.normSq_eq_norm_sq]]
  rw [hp]
  simp_rw [show ∀ h : Eisenstein,
    (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ))=
    (Real.pi/t:ℝ)*((Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
      (Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ)) from fun _ => by ring]
  rw [tsum_mul_left,←mul_assoc]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarGaussianError
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shift-independent error bound for scalar Poisson summation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTwistedGaussian_summable (χ : Eisenstein → ℂ)
    (hχ : ∀ a, ‖χ a‖≤1) {t : ℝ} (ht : 0<t) :
    Summable (fun a => χ a*(Real.exp (-t*norm a):ℂ)) := by
  have hA := residueHeckeScale_pos (q:=1) one_ne_zero
  have hs := principalLatticeTheta_summable (mul_pos ht hA)
  have hreal : Summable (fun a : Eisenstein => Real.exp (-t*norm a)) := by
    convert hs.norm using 1
    all_goals try with_reducible_and_instances rfl
    ext a
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    congr 1
    field_simp
  apply hreal.of_norm_bounded
  intro a
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ a)

lemma cubicThetaTwistedGaussian_error (χ : Eisenstein → ℂ)
    (hχ : ∀ a, ‖χ a‖≤1) (h0 : χ 0=1) {t : ℝ} (ht : 0<t) :
    ‖(∑' a : Eisenstein,χ a*(Real.exp (-t*norm a):ℂ))-1‖ ≤
      cubicThetaLatticeGaussianTail t := by
  classical
  have hs := cubicThetaTwistedGaussian_summable χ hχ ht
  have he : (∑' a : Eisenstein,χ a*(Real.exp (-t*norm a):ℂ))-1=
      ∑' a : {a : Eisenstein // a≠0},χ a.val*(Real.exp (-t*norm a.val):ℂ) := by
    rw [hs.tsum_eq_add_tsum_ite 0]
    simp only [h0,show norm (0:Eisenstein)=0 by simp [norm],mul_zero,Real.exp_zero,Complex.ofReal_one,
      one_mul,add_sub_cancel_left]
    calc
      _ = ∑' a : Eisenstein,Set.indicator {a : Eisenstein | a≠0}
          (fun a => χ a*(Real.exp (-t*norm a):ℂ)) a := by
        apply tsum_congr
        intro a
        by_cases ha : a=0 <;> simp [ha,Set.indicator]
      _ = _ := (tsum_subtype {a : Eisenstein | a≠0}
        (fun a => χ a*(Real.exp (-t*norm a):ℂ))).symm
  rw [he]
  have hh := hs.subtype (fun a : Eisenstein => a≠0)
  calc
    _ ≤ ∑' a : {a : Eisenstein // a≠0},‖χ a.val*(Real.exp (-t*norm a.val):ℂ)‖ :=
      norm_tsum_le_tsum_norm hh.norm
    _ ≤ cubicThetaLatticeGaussianTail t := by
      apply hh.norm.tsum_le_tsum _ (cubicThetaLatticeGaussianTail_summable ht)
      intro a
      dsimp only [Function.comp_apply]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ a.val)

theorem cubicThetaScalarGaussian_error (z : ℂ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaScalarGaussian z t-(2*Real.pi/(9*Real.sqrt 3*t):ℝ)‖ ≤
      (2*Real.pi/(9*Real.sqrt 3*t))*
        cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t)) := by
  let χ : Eisenstein → ℂ := fun h =>
    (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)
  have hχ (a : Eisenstein) : ‖χ a‖≤1 := (Circle.norm_coe _).le
  have h0 : χ 0=1 := by simp [χ,tracePair]
  have hk : 0≤2*Real.pi/(9*Real.sqrt 3*t) := by positivity
  have he := cubicThetaTwistedGaussian_error χ hχ h0 (t:=4*Real.pi^2/(27*t)) (by positivity)
  rw [cubicThetaScalarGaussian_poisson z ht,←mul_sub_one,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left he hk

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarGaussianReal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real positive form of the scalar lattice Gaussian and its uniform bound. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScalarGaussianReal_cast (z : ℂ) (t : ℝ) :
    (cubicThetaScalarGaussianReal z t:ℂ)=cubicThetaScalarGaussian z t := by
  exact Complex.ofReal_tsum _

lemma cubicThetaScalarGaussianReal_summable (z : ℂ) {t : ℝ} (ht : 0<t) :
    Summable (fun a : Eisenstein => Real.exp (-t*Complex.normSq (z+3*(a:ℂ)))) := by
  convert (cubicThetaScalarGaussian_summable z ht).norm using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

lemma cubicThetaScalarGaussianReal_nonneg (z : ℂ) (t : ℝ) :
    0 ≤ cubicThetaScalarGaussianReal z t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma cubicThetaScalarGaussianReal_error (z : ℂ) {t : ℝ} (ht : 0<t) :
    |cubicThetaScalarGaussianReal z t-2*Real.pi/(9*Real.sqrt 3*t)|≤
      (2*Real.pi/(9*Real.sqrt 3*t))*cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t)) := by
  have h := cubicThetaScalarGaussian_error z ht
  rw [←cubicThetaScalarGaussianReal_cast,←Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

lemma cubicThetaScalarGaussianReal_le (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussianReal z t≤(2*Real.pi/(9*Real.sqrt 3*t))*
      (1+cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t))) := by
  have h := (le_abs_self _).trans (cubicThetaScalarGaussianReal_error z ht)
  linarith

lemma cubicThetaScalarGaussianReal_zero_summand (a : Eisenstein) (t : ℝ) :
    Real.exp (-t*Complex.normSq (0+3*(a:ℂ)))=Real.exp (-9*t*norm a) := by
  rw [zero_add,Complex.normSq_mul,show Complex.normSq (3:ℂ)=9 by
    norm_num [Complex.normSq_apply]]
  congr 1
  change -t*(9*norm a)=_
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianLinearTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform inverse-linear bound for the nonzero lattice heat sum.
It controls the nonzero first coordinate in the reduced cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaScalarGaussianReal_zero_tail {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussianReal 0 (t/9)=1+cubicThetaLatticeGaussianTail t := by
  have hs : Summable (fun a : Eisenstein => Real.exp (-t*norm a)) := by
    convert cubicThetaScalarGaussianReal_summable 0 (div_pos ht (by norm_num : (0:ℝ)<9)) using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    congr 1
    ring
  have he : cubicThetaScalarGaussianReal 0 (t/9)=
      ∑' a : Eisenstein,Real.exp (-t*norm a) := by
    apply tsum_congr
    intro a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    congr 1
    ring
  rw [he,hs.tsum_eq_add_tsum_ite 0]
  simp only [show norm (0:Eisenstein)=0 by simp [norm],mul_zero,Real.exp_zero]
  congr 1
  calc
    _ = ∑' a : Eisenstein,Set.indicator {a : Eisenstein | a≠0}
        (fun a => Real.exp (-t*norm a)) a := by
      apply tsum_congr
      intro a
      by_cases ha : a=0 <;> simp [ha,Set.indicator]
    _ = _ := (tsum_subtype {a : Eisenstein | a≠0} (fun a => Real.exp (-t*norm a))).symm

lemma cubicThetaGaussianLinearConstant_nonneg : 0 ≤ cubicThetaGaussianLinearConstant := by
  unfold cubicThetaGaussianLinearConstant
  have h := cubicThetaGaussianPowerConstant_nonneg
  positivity

lemma cubicThetaLatticeGaussianTail_linear_bound {t : ℝ} (ht : 0<t) :
    cubicThetaLatticeGaussianTail t ≤ cubicThetaGaussianLinearConstant/t := by
  let D := cubicThetaGaussianPowerConstant
  let c := 4*Real.pi^2/3
  let A := (2*Real.pi/Real.sqrt 3)*(1+D/c^2)
  have hD : 0≤D := cubicThetaGaussianPowerConstant_nonneg
  have hA : 0≤A := by dsimp [A]; positivity
  change cubicThetaLatticeGaussianTail t≤(D+A)/t
  by_cases ht1 : t≤1
  · have hg := cubicThetaScalarGaussianReal_le 0 (div_pos ht (by norm_num : (0:ℝ)<9))
    rw [cubicThetaScalarGaussianReal_zero_tail ht] at hg
    have he : 4*Real.pi^2/(27*(t/9))=c/t := by dsimp [c]; ring
    have hk : 2*Real.pi/(9*Real.sqrt 3*(t/9))=(2*Real.pi/Real.sqrt 3)/t := by ring
    rw [he,hk] at hg
    have hT := cubicThetaLatticeGaussianTail_div_bound (c:=c) (by dsimp [c]; positivity) ht
    have ht2 : t^2≤1 := by nlinarith
    have hb : cubicThetaLatticeGaussianTail (c/t)≤D/c^2 :=
      hT.trans (by nlinarith [mul_nonneg (div_nonneg hD (sq_nonneg c)) (sub_nonneg.mpr ht2)])
    calc
      _ ≤ A/t := by
        have h := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hb)
          (show 0≤(2*Real.pi/Real.sqrt 3)/t by positivity)
        have hx : ((2*Real.pi/Real.sqrt 3)/t)*(1+D/c^2)=A/t := by dsimp [A]; ring
        rw [hx] at h
        linarith
      _ ≤ (D+A)/t := (div_le_div_iff_of_pos_right ht).mpr (by linarith)
  · have hlarge := cubicThetaLatticeGaussianTail_power_bound ht
    have ht1' : 1≤t := (lt_of_not_ge ht1).le
    apply hlarge.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos ht) ht).mpr
    nlinarith [mul_nonneg hD (sub_nonneg.mpr ht1'),mul_nonneg hA (sq_nonneg t)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspHeatBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Gaussian control of rows with nonzero first coordinate in a
fixed-height cusp. This estimate precedes the scalar Rankin domination. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScalarGaussian_uniform :
    ∃ C : ℝ, 1≤C ∧ ∀ z : ℂ, ∀ t : ℝ, 0<t →
      cubicThetaScalarGaussianReal z t≤C*(t+t⁻¹) := by
  let a := 2*Real.pi/(9*Real.sqrt 3)
  let c := 4*Real.pi^2/27
  let b := a*cubicThetaGaussianPowerConstant/c^2
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by
    dsimp only [b]
    exact div_nonneg (mul_nonneg ha cubicThetaGaussianPowerConstant_nonneg) (sq_nonneg c)
  refine ⟨1+a+b,by linarith,?_⟩
  intro z t ht
  have h := cubicThetaScalarGaussianReal_le z ht
  have htail := cubicThetaLatticeGaussianTail_div_bound (c:=c) (by dsimp [c]; positivity) ht
  have hpref : 2*Real.pi/(9*Real.sqrt 3*t)=a/t := by dsimp [a]; ring
  have harg : 4*Real.pi^2/(27*t)=c/t := by dsimp [c]; ring
  rw [hpref,harg] at h
  have h' : cubicThetaScalarGaussianReal z t≤a/t+b*t := by
    apply h.trans
    calc
      _ ≤ a/t*(1+(cubicThetaGaussianPowerConstant/c^2)*t^2) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) htail) (div_nonneg ha ht.le)
      _ = _ := by dsimp [b]; field_simp
  apply h'.trans
  have htinv : 0≤t⁻¹ := inv_nonneg.mpr ht.le
  rw [div_eq_mul_inv]
  nlinarith [mul_nonneg ha ht.le,mul_nonneg hb htinv]

lemma cubicThetaNonzeroFirstHeat_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    Summable (fun c : {c : Eisenstein // c≠0} => Real.exp (-(t*p.2)*norm c.val)*
      cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2))) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaScalarGaussian_uniform
  have hs := (cubicThetaLatticeGaussianTail_summable (mul_pos ht hp)).mul_right
    (C*(t/(9*p.2)+(t/(9*p.2))⁻¹))
  apply hs.of_nonneg_of_le
  · intro c
    exact mul_nonneg (Real.exp_pos _).le (cubicThetaScalarGaussianReal_nonneg _ _)
  · intro c
    exact mul_le_mul_of_nonneg_left (hbound _ _ (by positivity)) (Real.exp_pos _).le

lemma cubicThetaNonzeroFirstHeat_bound :
    ∃ D : ℝ, 0≤D ∧ ∀ p : ℂ × ℝ, 1/2≤p.2 → ∀ t : ℝ, 0<t →
      cubicThetaNonzeroFirstHeat p t≤D*(1+t⁻¹^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaScalarGaussian_uniform
  let L := cubicThetaGaussianLinearConstant
  have hL : 0≤L := cubicThetaGaussianLinearConstant_nonneg
  refine ⟨36*C*L,by positivity,?_⟩
  intro p hp t ht
  have hp0 : 0<p.2 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp
  have hmajor := (cubicThetaLatticeGaussianTail_summable (mul_pos ht hp0)).mul_right
    (C*(t/(9*p.2)+(t/(9*p.2))⁻¹))
  have hsum := (cubicThetaNonzeroFirstHeat_summable hp0 ht).tsum_le_tsum
    (fun c => mul_le_mul_of_nonneg_left (hbound _ _ (by positivity)) (Real.exp_pos _).le) hmajor
  rw [tsum_mul_right] at hsum
  have htail := cubicThetaLatticeGaussianTail_linear_bound (mul_pos ht hp0)
  have hfac : 0≤C*(t/(9*p.2)+(t/(9*p.2))⁻¹) := by positivity
  have h := hsum.trans (mul_le_mul_of_nonneg_right htail hfac)
  change cubicThetaNonzeroFirstHeat p t≤_ at h
  have he : L/(t*p.2)*(C*(t/(9*p.2)+(t/(9*p.2))⁻¹))=
      C*L*((1/9)/(p.2^2)+9/(t^2)) := by field_simp
  rw [he] at h
  apply h.trans
  have hv : (1/9:ℝ)/(p.2^2)≤4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    nlinarith
  rw [inv_pow]
  have hn : 0≤(t^2)⁻¹ := inv_nonneg.mpr (sq_nonneg t)
  have hx : (1/9:ℝ)/(p.2^2)+9/(t^2)≤36*(1+(t^2)⁻¹) := by
    rw [div_eq_mul_inv (9:ℝ)]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hx (mul_nonneg (by linarith : 0≤C) hL)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarEisenstein
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Eisenstein series for the same principal arithmetic group.
It supplies the positive height kernel for the energy unfolding. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScalarEisenstein_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r : CubicThetaBottomRow => (r.height p:ℂ)^s) := by
  apply Summable.of_norm
  apply (cubicThetaEisenstein_summable hp hs).norm.congr
  intro r
  simp only [cubicThetaEisensteinTerm,norm_mul,norm_star,r.phase_norm,one_mul]

lemma cubicThetaScalarEisenstein_real_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    Summable (fun r : CubicThetaBottomRow => r.height p^s) := by
  have h := (cubicThetaScalarEisenstein_summable hp (s:=(s:ℂ)) (by simpa using hs)).norm
  apply h.congr
  intro r
  exact Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularHeatPole
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar row Mellin transform has the exact pole supplied by the
four-dimensional affine lattice. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeatPole_integral {s : ℝ} (hs : 2 < s) :
    (∫ t in Ioc (0:ℝ) 1,t^(s-3))=1/(s-2) := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1 < s-3))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : s-3+1≠0)]
  congr 1 <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullMassResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the full affine-row norm series. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRealGamma_continuousAt_two : ContinuousAt Real.Gamma 2 := by
  have h : ContinuousAt Complex.Gamma (2:ℂ) := Complex.continuousAt_Gamma 2 (by
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith)
  have hc : ContinuousAt (fun s : ℝ => Complex.Gamma (s:ℂ)) 2 :=
    h.comp (f:=fun s : ℝ => (s:ℂ)) Complex.continuous_ofReal.continuousAt
  exact Complex.continuous_re.continuousAt.comp
    (f:=fun s : ℝ => Complex.Gamma (s:ℂ)) hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroRowHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal two-coordinate Gaussian behind the nonzero-first-row bound. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNonzeroRowHeatTerm_factor {p : ℂ × ℝ} (hp : 0<p.2)
    (t : ℝ) (c : {c : Eisenstein // c≠0}) (d : Eisenstein) :
    cubicThetaNonzeroRowHeatTerm p t (c,d)=Real.exp (-(t*p.2)*norm c.val)*
      Real.exp (-(t/(9*p.2))*Complex.normSq (3*(c.val:ℂ)*p.1+3*(d:ℂ))) := by
  have he : 3*(c.val:ℂ)*p.1+3*(d:ℂ)=3*((c.val:ℂ)*p.1+d) := by ring
  rw [he,Complex.normSq_mul,show Complex.normSq (3:ℂ)=9 by norm_num]
  rw [←Real.exp_add]
  unfold cubicThetaNonzeroRowHeatTerm cubicThetaNonzeroRowQuadratic
  congr 1
  field_simp
  ring

lemma cubicThetaNonzeroRowHeatTerm_row_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) (c : {c : Eisenstein // c≠0}) :
    Summable (fun d : Eisenstein => cubicThetaNonzeroRowHeatTerm p t (c,d)) := by
  simp_rw [cubicThetaNonzeroRowHeatTerm_factor hp]
  exact (cubicThetaScalarGaussianReal_summable (3*(c.val:ℂ)*p.1) (by positivity)).mul_left _

lemma cubicThetaNonzeroRowHeatTerm_row (p : ℂ × ℝ) (hp : 0<p.2)
    (t : ℝ) (c : {c : Eisenstein // c≠0}) :
    (∑' d : Eisenstein,cubicThetaNonzeroRowHeatTerm p t (c,d))=
      Real.exp (-(t*p.2)*norm c.val)*cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2)) := by
  simp_rw [cubicThetaNonzeroRowHeatTerm_factor hp]
  rw [tsum_mul_left]
  rfl

lemma cubicThetaNonzeroRowHeatTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) : Summable (cubicThetaNonzeroRowHeatTerm p t) := by
  apply (summable_prod_of_nonneg (f:=cubicThetaNonzeroRowHeatTerm p t)
    (fun r => (Real.exp_pos _).le)).mpr
  constructor
  · exact cubicThetaNonzeroRowHeatTerm_row_summable hp ht
  · simp_rw [cubicThetaNonzeroRowHeatTerm_row p hp]
    exact cubicThetaNonzeroFirstHeat_summable hp ht

theorem cubicThetaNonzeroRowHeatTerm_tsum {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaNonzeroRow,cubicThetaNonzeroRowHeatTerm p t r)=
      cubicThetaNonzeroFirstHeat p t := by
  rw [(cubicThetaNonzeroRowHeatTerm_summable hp ht).tsum_prod]
  simp_rw [cubicThetaNonzeroRowHeatTerm_row p hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right action of the full integral modular group on primitive rows.
This transports the positive scalar cutoff into a fixed Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma CubicThetaPrimitiveRow.height_rightMul (r : CubicThetaPrimitiveRow)
    (g : SL(2,Eisenstein)) {p : ℂ × ℝ} (hp : 0<p.2) :
    (r.rightMul g).height p=r.height (cubicThetaMobius (cubicThetaFullComplex g) p) := by
  rw [CubicThetaPrimitiveRow.rightMul,cubicThetaPrimitiveRow_height,map_mul,
    ←cubicThetaMobius_comp _ _ hp,←cubicThetaPrimitiveRow_height,r.completion_row]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarHeightCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the finitely many rows above height one preserves the scalar
Eisenstein pole. The remaining positive kernel is the one used in the
Rankin integral of the square-integrable theta section. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaScalarHeightCutoff_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    Summable (fun r : CubicThetaBottomRow => if r.height p≤1 then r.height p^s else 0) := by
  apply (cubicThetaScalarEisenstein_real_summable hp hs).of_nonneg_of_le
  · intro r
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl
  · intro r
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (r.height_pos hp).le _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive truncated scalar kernel on the actual arithmetic quotient.
Its residue is known before any integration against the theta norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_3 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaBottomRow : Countable CubicThetaBottomRow := by
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r s h
    exact CubicThetaBottomRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  exact hi.countable

lemma cubicThetaScalarHeightCutoff_nonneg {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    0 ≤ cubicThetaScalarHeightCutoff p s := by
  apply tsum_nonneg
  intro r
  split_ifs
  · exact Real.rpow_nonneg (r.height_pos hp).le _
  · exact le_rfl

lemma cubicThetaScalarHeightCutoff_invariant (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    cubicThetaScalarHeightCutoff (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaScalarHeightCutoff p s := by
  unfold cubicThetaScalarHeightCutoff
  simp_rw [←CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq
    (fun r => if r.height p≤1 then r.height p^s else (0:ℝ))

lemma cubicThetaScalarHeightCutoff_point_measurable (s : ℝ) :
    Measurable (fun p : CubicThetaPoint => cubicThetaScalarHeightCutoff p.val s) := by
  apply Measurable.tsum
  intro r
  have hc : Continuous (fun p : CubicThetaPoint => r.height p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (r.height_contDiffAt p.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  apply Measurable.ite (measurableSet_le hc.measurable measurable_const)
  · exact (hc.rpow_const (fun p => Or.inl (r.height_pos p.property).ne')).measurable
  · exact measurable_const

lemma cubicThetaScalarRankinKernel_measurable (σ : ℝ) :
    Measurable (cubicThetaScalarRankinKernel σ) :=
  (cubicThetaScalarHeightCutoff_point_measurable _).comp cubicThetaBorelSection_measurable

lemma cubicThetaScalarRankinKernel_nonneg (σ : ℝ) (q : CubicThetaQuotient) :
    0 ≤ cubicThetaScalarRankinKernel σ q :=
  cubicThetaScalarHeightCutoff_nonneg (cubicThetaBorelSection q).property _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive full-group kernel majorizing the principal scalar kernel.
Its right action allows the estimate to be proved in one Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaPrimitiveRow.norm_le_denominator (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    1+norm r.c+norm r.d ≤ cubicThetaHeightConstant p*r.denominator p := by
  have hnorm : 1 ≤ norm r.c+norm r.d := by
    rcases r.coprime.ne_zero_or_ne_zero with hc | hd
    · linarith [one_le_norm hc,norm_nonneg r.d]
    · linarith [one_le_norm hd,norm_nonneg r.c]
  have h := r.norm_sum_bound hp
  unfold cubicThetaHeightConstant
  nlinarith

lemma CubicThetaPrimitiveRow.height_le (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height p ≤ (p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d) := by
  apply (div_le_div_iff₀ (r.denominator_pos hp) (by linarith [norm_nonneg r.c,norm_nonneg r.d])).mpr
  have h := mul_le_mul_of_nonneg_left (r.norm_le_denominator hp) hp.le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma cubicThetaPrimitiveHeight_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) : Summable (fun r : CubicThetaPrimitiveRow => r.height p^s) := by
  have hC := cubicThetaHeightConstant_pos hp
  have hsum := summable_eisenstein_one_add_norm (show 1 < s/2 by linarith)
  have hprod : Summable (fun cd : Eisenstein × Eisenstein =>
      (1+norm cd.1)^(-(s/2))*(1+norm cd.2)^(-(s/2))) :=
    summable_mul_of_summable_norm hsum.norm hsum.norm
  have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
    intro r t h
    exact CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  apply ((hprod.mul_left ((p.2*cubicThetaHeightConstant p)^s)).comp_injective hi).of_nonneg_of_le
  · intro r
    exact Real.rpow_nonneg (r.height_pos hp).le _
  · intro r
    dsimp only [Function.comp_apply]
    have hN : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
    calc
      _  ≤  ((p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d))^s :=
        Real.rpow_le_rpow (r.height_pos hp).le (r.height_le hp) (by linarith)
      _ = (p.2*cubicThetaHeightConstant p)^s*(1+norm r.c+norm r.d)^(-s) := by
        rw [Real.div_rpow (mul_pos hp hC).le hN.le,Real.rpow_neg hN.le]
        rfl
      _  ≤  _ := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_left
          (cubicTheta_two_norm_decay (norm_nonneg r.c) (norm_nonneg r.d) (by linarith : 0 ≤ s))
          (Real.rpow_nonneg (mul_pos hp hC).le _)

lemma cubicThetaPrimitiveKernel_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    Summable (fun r : CubicThetaPrimitiveRow => if r.height p ≤ 1 then r.height p^s else 0) := by
  apply (cubicThetaPrimitiveHeight_summable hp hs).of_nonneg_of_le
  · intro r
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl
  · intro r
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (r.height_pos hp).le _

lemma cubicThetaScalarHeightCutoff_le_primitive {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) : cubicThetaScalarHeightCutoff p s ≤ cubicThetaPrimitiveKernel p s := by
  let f : CubicThetaBottomRow → CubicThetaPrimitiveRow := fun r => ⟨r.c,r.d,r.coprime⟩
  have hi : Function.Injective f := by
    intro r t h
    exact CubicThetaBottomRow.ext (congrArg CubicThetaPrimitiveRow.c h)
      (congrArg CubicThetaPrimitiveRow.d h)
  have hsum := cubicThetaPrimitiveKernel_summable hp hs
  have hpull := hsum.comp_injective hi
  have h := hpull.tsum_le_tsum_of_inj f hi (fun r _ => by
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl) (fun r => le_rfl) hsum
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive heat representation of the truncated primitive kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_4 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaPrimitiveRow : Countable CubicThetaPrimitiveRow := by
  have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
    intro r s h
    exact CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  exact hi.countable

lemma cubicThetaPrimitiveHeatTerm_nonneg (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaPrimitiveRow) :
    0 ≤ cubicThetaPrimitiveHeatTerm p t r := by
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma cubicThetaPrimitiveHeat_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) : Summable (cubicThetaPrimitiveHeatTerm p t) := by
  have hsum := (cubicThetaPrimitiveHeight_summable hp (s:=3) (by norm_num)).mul_left (6/t^3)
  apply hsum.of_nonneg_of_le (cubicThetaPrimitiveHeatTerm_nonneg p t)
  intro r
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · have hx := r.height_pos hp
    have hi := power_exp_bound ht 3 (r.height p)⁻¹ (inv_pos.mpr hx).le
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
      Nat.cast_ofNat,mul_one] at hi
    rw [Real.rpow_ofNat]
    have hh : Real.exp (-t/r.height p)=Real.exp (-t*(r.height p)⁻¹) := by rw [div_eq_mul_inv]
    rw [hh]
    apply (div_le_iff₀ (pow_pos hx 3)).mp
    simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hi
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (r.height_pos hp).le _)

lemma cubicThetaPrimitiveHeatMellinTerm_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaPrimitiveRow) :
    IntegrableOn (cubicThetaPrimitiveHeatMellinTerm p s r) (Ioi 0) := by
  unfold cubicThetaPrimitiveHeatMellinTerm cubicThetaPrimitiveHeatTerm
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr]
    convert integrable_laplace_rpow hs (inv_pos.mpr (r.height_pos hp)) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    congr 2
    rw [div_eq_mul_inv]
    ring
  · simp only [ite_eq_right hr,mul_zero]
    exact integrableOn_zero

lemma cubicThetaPrimitiveHeatMellinTerm_integral {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaPrimitiveRow) :
    (∫ t in Ioi (0:ℝ),cubicThetaPrimitiveHeatMellinTerm p s r t)=
      Real.Gamma s*(if r.height p≤1 then r.height p^s else 0) := by
  unfold cubicThetaPrimitiveHeatMellinTerm cubicThetaPrimitiveHeatTerm
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr]
    have he : ∀ t : ℝ,-t/r.height p= -(r.height p)⁻¹*t := by intro t; rw [div_eq_mul_inv]; ring
    simp_rw [he]
    rw [laplace_rpow hs (inv_pos.mpr (r.height_pos hp)),
      Real.inv_rpow (r.height_pos hp).le,Real.rpow_neg (r.height_pos hp).le,inv_inv]
  · simp only [ite_eq_right hr,mul_zero,integral_zero]

lemma cubicThetaPrimitiveHeatMellinTerm_mass {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaPrimitiveRow) :
    (∫ t in Ioi (0:ℝ),‖cubicThetaPrimitiveHeatMellinTerm p s r t‖)=
      Real.Gamma s*(if r.height p≤1 then r.height p^s else 0) := by
  rw [←cubicThetaPrimitiveHeatMellinTerm_integral hp hs r]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
    (cubicThetaPrimitiveHeatTerm_nonneg p t r))

theorem cubicThetaPrimitiveKernel_heat_mellin {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t)=
      Real.Gamma s*cubicThetaPrimitiveKernel p s := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hmass : Summable (fun r : CubicThetaPrimitiveRow =>
      ∫ t in Ioi (0:ℝ),‖cubicThetaPrimitiveHeatMellinTerm p s r t‖) := by
    simp_rw [cubicThetaPrimitiveHeatMellinTerm_mass hp hs0]
    exact (cubicThetaPrimitiveKernel_summable hp hs).mul_left _
  calc
    _ = ∫ t in Ioi (0:ℝ),∑' r : CubicThetaPrimitiveRow,cubicThetaPrimitiveHeatMellinTerm p s r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [cubicThetaPrimitiveHeat,←tsum_mul_left]
      rfl
    _ = ∑' r : CubicThetaPrimitiveRow,∫ t in Ioi (0:ℝ),cubicThetaPrimitiveHeatMellinTerm p s r t :=
      (integral_tsum_of_summable_integral_norm
        (fun r => cubicThetaPrimitiveHeatMellinTerm_integrable hp hs0 r) hmass).symm
    _ = _ := by
      simp_rw [cubicThetaPrimitiveHeatMellinTerm_integral hp hs0]
      rw [tsum_mul_left]
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveZeroRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-first-coordinate rows are exactly the finitely many units.
Their cutoff heat contribution has uniform exponential decay. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaUnitRow_height (u : Eisensteinˣ) (p : ℂ × ℝ) :
    (cubicThetaUnitRow u).val.height p=p.2 := by
  change p.2/(Complex.normSq ((0:ℂ)*p.1+((u:Eisenstein):ℂ))+norm (0:Eisenstein)*p.2^2)=p.2
  rw [zero_mul,zero_add,show Complex.normSq ((u:Eisenstein):ℂ)=1 from norm_of_isUnit u.isUnit]
  simp [norm]

lemma cubicThetaZeroFirstRows_finite : Finite CubicThetaZeroFirstRow := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  exact Finite.of_equiv (Eisensteinˣ) cubicThetaZeroFirstRowEquiv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeatCusp
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform control of the actual truncated primitive heat kernel in a cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaNonzeroFirstPrimitiveRow_map_injective :
    Function.Injective cubicThetaNonzeroFirstPrimitiveRow_map := by
  intro r q h
  apply Subtype.ext
  apply CubicThetaPrimitiveRow.ext
  · exact congrArg (fun r : CubicThetaNonzeroRow => r.1.val) h
  · exact congrArg (fun r : CubicThetaNonzeroRow => r.2) h

lemma cubicThetaPrimitiveHeatTerm_le_nonzero {p : ℂ × ℝ} (hp : 0<p.2)
    (t : ℝ) (r : CubicThetaNonzeroFirstPrimitiveRow) :
    cubicThetaPrimitiveHeatTerm p t r.val ≤
      cubicThetaNonzeroRowHeatTerm p t (cubicThetaNonzeroFirstPrimitiveRow_map r) := by
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · apply le_of_eq
    unfold cubicThetaNonzeroRowHeatTerm cubicThetaNonzeroRowQuadratic
      cubicThetaNonzeroFirstPrimitiveRow_map CubicThetaPrimitiveRow.height
      CubicThetaPrimitiveRow.denominator
    congr 1
    field_simp
  · exact (Real.exp_pos _).le

lemma cubicThetaPrimitiveHeat_nonzero_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaNonzeroFirstPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r.val) ≤
      cubicThetaNonzeroFirstHeat p t := by
  have hs := (cubicThetaPrimitiveHeat_summable hp ht).comp_injective
    (Subtype.val_injective (p:=fun r : CubicThetaPrimitiveRow => r.c≠0))
  have hfull := cubicThetaNonzeroRowHeatTerm_summable hp ht
  rw [←cubicThetaNonzeroRowHeatTerm_tsum hp ht]
  exact hs.tsum_le_tsum_of_inj cubicThetaNonzeroFirstPrimitiveRow_map
    cubicThetaNonzeroFirstPrimitiveRow_map_injective (fun _ _ => (Real.exp_pos _).le)
    (cubicThetaPrimitiveHeatTerm_le_nonzero hp t) hfull

lemma cubicThetaPrimitiveHeat_zero_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaZeroFirstRow,cubicThetaPrimitiveHeatTerm p t r.val) ≤
      (Nat.card CubicThetaZeroFirstRow:ℝ)*Real.exp (-t) := by
  let : Finite CubicThetaZeroFirstRow := cubicThetaZeroFirstRows_finite
  let : Fintype CubicThetaZeroFirstRow := Fintype.ofFinite _
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _r : CubicThetaZeroFirstRow,Real.exp (-t) := by
      apply Finset.sum_le_sum
      intro r _
      obtain ⟨u,rfl⟩ := cubicThetaUnitRow_surjective r
      unfold cubicThetaPrimitiveHeatTerm
      rw [cubicThetaUnitRow_height]
      split_ifs with hv
      · apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hp).mpr
        nlinarith
      · exact (Real.exp_pos _).le
    _ = _ := by simp [Nat.card_eq_fintype_card]

theorem cubicThetaPrimitiveHeat_cusp_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 1/2≤p.2 → ∀ t : ℝ, 0<t →
      cubicThetaPrimitiveHeat p t ≤ C*(1+t⁻¹^2) := by
  obtain ⟨D,hD,hbound⟩ := cubicThetaNonzeroFirstHeat_bound
  let n : ℝ := Nat.card CubicThetaZeroFirstRow
  have hn : 0≤n := Nat.cast_nonneg _
  refine ⟨n+D,add_nonneg hn hD,?_⟩
  intro p hp t ht
  have hp0 : 0<p.2 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp
  have he := (cubicThetaPrimitiveHeat_summable hp0 ht).tsum_subtype_add_tsum_subtype_compl
    {r : CubicThetaPrimitiveRow | r.c=0}
  have hb := add_le_add (cubicThetaPrimitiveHeat_zero_bound hp0 ht)
    (cubicThetaPrimitiveHeat_nonzero_bound hp0 ht)
  change _ ≤ n*Real.exp (-t)+cubicThetaNonzeroFirstHeat p t at hb
  change (∑' r : CubicThetaZeroFirstRow,cubicThetaPrimitiveHeatTerm p t r.val)+
    (∑' r : CubicThetaNonzeroFirstPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r.val)=
      cubicThetaPrimitiveHeat p t at he
  rw [he] at hb
  change cubicThetaPrimitiveHeat p t ≤ _ at hb
  apply hb.trans
  have hexp : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hzero := mul_le_mul_of_nonneg_left hexp hn
  have hnonzero := hbound p hp t ht
  have ht2 : 0≤t⁻¹^2 := sq_nonneg _
  nlinarith [mul_nonneg hn ht2]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeatDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-group reduction and exponential decay for the truncated row heat. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimitiveHeat_nonneg (p : ℂ × ℝ) (t : ℝ) :
    0 ≤ cubicThetaPrimitiveHeat p t := tsum_nonneg (cubicThetaPrimitiveHeatTerm_nonneg p t)

lemma cubicThetaPrimitiveHeat_invariant (g : SL(2,Eisenstein))
    {p : ℂ × ℝ} (hp : 0<p.2) (t : ℝ) :
    cubicThetaPrimitiveHeat (cubicThetaMobius (cubicThetaFullComplex g) p) t=
      cubicThetaPrimitiveHeat p t := by
  unfold cubicThetaPrimitiveHeat cubicThetaPrimitiveHeatTerm
  simp_rw [←CubicThetaPrimitiveRow.height_rightMul _ g hp]
  exact (CubicThetaPrimitiveRow.rightMulEquiv g).tsum_eq
    (fun r => if r.height p≤1 then Real.exp (-t/r.height p) else (0:ℝ))

theorem cubicThetaPrimitiveHeat_uniform :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 0<p.2 → ∀ t : ℝ, 0<t →
      cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_cusp_bound
  refine ⟨C,hC,?_⟩
  intro p hp t ht
  obtain ⟨g,hg⟩ := cubicThetaSiegelSet_meets_orbit hp
  have h := hbound _ hg.2.2 t ht
  rwa [cubicThetaPrimitiveHeat_invariant g hp] at h

lemma cubicThetaPrimitiveHeat_half {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    cubicThetaPrimitiveHeat p t≤Real.exp (-t/2)*cubicThetaPrimitiveHeat p (t/2) := by
  have hh : 0<t/2 := by linarith
  have hs := (cubicThetaPrimitiveHeat_summable hp hh).mul_left (Real.exp (-t/2))
  calc
    _ ≤ ∑' r : CubicThetaPrimitiveRow,Real.exp (-t/2)*cubicThetaPrimitiveHeatTerm p (t/2) r := by
      apply (cubicThetaPrimitiveHeat_summable hp ht).tsum_le_tsum _ hs
      intro r
      unfold cubicThetaPrimitiveHeatTerm
      split_ifs with hr
      · rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hx := r.height_pos hp
        have hi : 1≤(r.height p)⁻¹ := (one_le_inv₀ hx).mpr hr
        simp only [div_eq_mul_inv]
        nlinarith
      · simp only [mul_zero,le_refl]
    _ = _ := by rw [tsum_mul_left]; rfl

theorem cubicThetaPrimitiveHeat_small_large :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 0<p.2 →
      (∀ t : ℝ, 0<t → cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2)) ∧
      (∀ t : ℝ, 1≤t → cubicThetaPrimitiveHeat p t≤5*C*Real.exp (-t/2)) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_uniform
  refine ⟨C,hC,?_⟩
  intro p hp
  refine ⟨hbound p hp,?_⟩
  intro t ht
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have h := (cubicThetaPrimitiveHeat_half hp ht0).trans
    (mul_le_mul_of_nonneg_left (hbound p hp (t/2) (by linarith)) (Real.exp_pos _).le)
  have hinv : (t/2)⁻¹≤2 := by
    have hh : 0<t/2 := by linarith
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hh).mpr
    linarith
  have hpow : (t/2)⁻¹^2≤4 := by nlinarith [inv_nonneg.mpr (by linarith : 0≤t/2)]
  have hC' := mul_le_mul_of_nonneg_left (show 1+(t/2)⁻¹^2≤5 by linarith) hC
  have h' := mul_le_mul_of_nonneg_left hC' (Real.exp_pos (-t/2)).le
  exact h.trans (by nlinarith [h'])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatMellinBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable small- and large-time majorants for the primitive heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_5 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaPrimitiveRow_1 : Countable CubicThetaPrimitiveRow := by
  exact (show Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) from
    fun r q h => CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2).countable

lemma cubicThetaPrimitiveHeat_measurable (p : ℂ × ℝ) :
    Measurable (cubicThetaPrimitiveHeat p) := by
  apply Measurable.tsum
  intro r
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs <;> fun_prop

lemma cubicThetaPrimitiveMellin_measurable (p : ℂ × ℝ) (s : ℝ) :
    Measurable (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) := by
  have hm := cubicThetaPrimitiveHeat_measurable p
  fun_prop

lemma cubicThetaPrimitiveMellin_low_bound {p : ℂ × ℝ} {s C t : ℝ}
    (hC : 0≤C) (ht : t∈Ioc (0:ℝ) 1)
    (hheat : cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2)) :
    ‖t^(s-1)*cubicThetaPrimitiveHeat p t‖≤2*C*t^(s-3) := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
    (cubicThetaPrimitiveHeat_nonneg p t))]
  have hinv : 1≤t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
  have htwo : 1+t⁻¹^2≤2*t⁻¹^2 := by nlinarith
  have hb := hheat.trans (mul_le_mul_of_nonneg_left htwo hC)
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1.le (s-1))
  apply hm.trans_eq
  have he : t^(s-1)*t⁻¹^2=t^(s-3) := by
    rw [inv_pow,←Real.rpow_two,←Real.rpow_neg ht.1.le,←Real.rpow_add ht.1]
    congr 1
    ring
  calc
    t^(s-1)*(C*(2*t⁻¹^2))=2*C*(t^(s-1)*t⁻¹^2) := by ring
    _ = _ := by rw [he]

lemma cubicThetaPrimitiveMellin_high_bound {p : ℂ × ℝ} {s C t : ℝ}
    (hC : 0≤C) (hs : s≤3) (ht : 1<t)
    (hheat : cubicThetaPrimitiveHeat p t≤5*C*Real.exp (-t/2)) :
    ‖t^(s-1)*cubicThetaPrimitiveHeat p t‖≤5*C*(t^2*Real.exp (-t/2)) := by
  have ht0 : 0<t := lt_trans zero_lt_one ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
    (cubicThetaPrimitiveHeat_nonneg p t))]
  have hpow : t^(s-1)≤t^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hheat (Real.rpow_nonneg ht0.le (s-1))
  have hfac : 0≤5*C*Real.exp (-t/2) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hpow hfac
  exact h1.trans (by nlinarith [h2])

lemma cubicThetaPrimitiveMellin_tail_integrable :
    IntegrableOn (fun t : ℝ => t^2*Real.exp (-t/2)) (Ioi 0) := by
  convert integrable_laplace_rpow (by norm_num : (0:ℝ)<3)
    (by norm_num : (0:ℝ)<1/2) using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [show (3:ℝ)-1=2 by norm_num,Real.rpow_two]
  congr 2
  ring

lemma cubicThetaPrimitiveMellinTailMass_nonneg : 0 ≤ cubicThetaPrimitiveMellinTailMass := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (sq_nonneg t) (Real.exp_pos _).le

lemma cubicThetaPrimitiveMellin_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) (hs3 : s≤3) :
    IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_small_large
  have hlow : IntegrableOn (fun t : ℝ => 2*C*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s-3))).const_mul _
  have hhigh : IntegrableOn (fun t : ℝ => 5*C*(t^2*Real.exp (-t/2))) (Ioi 1) :=
    (cubicThetaPrimitiveMellin_tail_integrable.mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).const_mul _
  have hl : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioc 0 1) := by
    apply hlow.mono' (cubicThetaPrimitiveMellin_measurable p s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact cubicThetaPrimitiveMellin_low_bound hC ht ((hbound p hp).1 t ht.1)
  have hh : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioi 1) := by
    apply hhigh.mono' (cubicThetaPrimitiveMellin_measurable p s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaPrimitiveMellin_high_bound hC hs3 ht ((hbound p hp).2 t ht.le)
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] using hl.union hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveKernelBound
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform bound for the normalized primitive kernel at its pole.
The only inputs are the proved lattice Gaussian estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaPrimitiveKernel_nonneg {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    0 ≤ cubicThetaPrimitiveKernel p s := by
  apply tsum_nonneg
  intro r
  split_ifs
  · exact Real.rpow_nonneg (r.height_pos hp).le _
  · exact le_rfl

theorem cubicThetaPrimitiveKernel_gamma_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℂ × ℝ, 0<p.2 → ∀ s : ℝ, 2 < s → s ≤ 3 →
      (s-2)*Real.Gamma s*cubicThetaPrimitiveKernel p s ≤ D := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_small_large
  let H := cubicThetaPrimitiveMellinTailMass
  have hH : 0 ≤ H := cubicThetaPrimitiveMellinTailMass_nonneg
  refine ⟨2*C+5*C*H,by positivity,?_⟩
  intro p hp s hs hs3
  have hf := cubicThetaPrimitiveMellin_integrable hp hs hs3
  have hflo : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaPrimitiveHeat p t) (Ioc 0 1) :=
    hf.mono_set Ioc_subset_Ioi_self
  have hfhi := hf.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hglo : IntegrableOn (fun t : ℝ => 2*C*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s-3))).const_mul _
  have hghi : IntegrableOn (fun t : ℝ => 5*C*(t^2*Real.exp (-t/2))) (Ioi 1) :=
    (cubicThetaPrimitiveMellin_tail_integrable.mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))).const_mul _
  have hlo := setIntegral_mono_on hflo hglo measurableSet_Ioc (fun t ht =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      cubicThetaPrimitiveMellin_low_bound hC ht ((hbound p hp).1 t ht.1)))
  have hhi := setIntegral_mono_on hfhi hghi measurableSet_Ioi (fun t ht =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      cubicThetaPrimitiveMellin_high_bound hC hs3 ht ((hbound p hp).2 t ht.le)))
  rw [integral_const_mul,cubicThetaHeatPole_integral hs] at hlo
  rw [integral_const_mul] at hhi
  change _ ≤ 5*C*H at hhi
  have he : (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t)=
      (∫ t in Ioc (0:ℝ) 1,t^(s-1)*cubicThetaPrimitiveHeat p t)+
        ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hflo hfhi]
  rw [cubicThetaPrimitiveKernel_heat_mellin hp hs] at he
  have hsum := add_le_add hlo hhi
  rw [←he] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ s-2 by linarith)
  have hc : (s-2)*(2*C*(1/(s-2))+5*C*H)=2*C+(s-2)*(5*C*H) := by
    field_simp [show s-2≠0 by linarith]
  rw [hc] at hm
  have hlast : (s-2)*(5*C*H) ≤ 5*C*H := by
    nlinarith [mul_nonneg hC hH]
  nlinarith

theorem cubicThetaPrimitiveKernel_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ s : ℝ in 𝓝[>] 2,
      ∀ p : ℂ × ℝ, 0<p.2 → (s-2)*cubicThetaPrimitiveKernel p s ≤ K := by
  obtain ⟨D,hD,hbound⟩ := cubicThetaPrimitiveKernel_gamma_bound
  refine ⟨2*D,by positivity,?_⟩
  have hG : ∀ᶠ s : ℝ in 𝓝 2,(1/2:ℝ)<Real.Gamma s := by
    have h := cubicThetaRealGamma_continuousAt_two.tendsto.eventually
      (Ioi_mem_nhds (show (1/2:ℝ)<Real.Gamma 2 by norm_num))
    exact h
  have h3 : ∀ᶠ s : ℝ in 𝓝 2,s<3 := Iio_mem_nhds (by norm_num)
  filter_upwards [hG.filter_mono nhdsWithin_le_nhds,
    h3.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hG hs3 hs
  change 2 < s at hs
  intro p hp
  have h := hbound p hp s hs hs3.le
  have hnonneg := mul_nonneg (show 0 ≤ s-2 by exact sub_nonneg.mpr hs.le)
    (cubicThetaPrimitiveKernel_nonneg hp s)
  have hm := mul_le_mul_of_nonneg_right hG.le hnonneg
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRankinConvergence
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated convergence of the actual truncated scalar kernel on the quotient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRankin_exponent_tendsto :
    Tendsto (fun σ : ℝ => 2+2*σ) (𝓝[>] 0) (𝓝[>] 2) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : ContinuousAt (fun σ : ℝ => 2+2*σ) 0 := by fun_prop
    simpa using h.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    change 0<σ at hσ
    change 2<2+2*σ
    linarith

theorem cubicThetaScalarRankinKernel_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 0,
      ∀ q : CubicThetaQuotient, ‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := cubicThetaPrimitiveKernel_uniform
  refine ⟨K,hK,?_⟩
  filter_upwards [cubicThetaRankin_exponent_tendsto.eventually hbound,
    self_mem_nhdsWithin] with σ hb hσ
  change 0<σ at hσ
  intro q
  let p := cubicThetaBorelSection q
  have hsc := cubicThetaScalarHeightCutoff_le_primitive p.property
    (show 2<2+2*σ by linarith)
  have hnonneg := cubicThetaScalarRankinKernel_nonneg σ q
  have hsmall := mul_le_mul_of_nonneg_left hsc hσ.le
  have hbig := hb p.val p.property
  change σ*cubicThetaScalarRankinKernel σ q ≤ σ*cubicThetaPrimitiveKernel p.val (2+2*σ) at hsmall
  rw [←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hσ.le hnonneg)]
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaModelRankinLimit
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Rankin pole paired with the actual global cubic theta section. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
namespace CubicFirstMoment

lemma cubicThetaArithmeticModelPairing_eq (q : CubicThetaQuotient) :
    cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection q=
      (‖cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q‖^2:ℂ) := by
  have h := cubicThetaSectionPairing_apply cubicThetaArithmeticModelSection
    cubicThetaArithmeticModelSection (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse,inner_self_eq_norm_sq_to_K] at h
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive unfolding on the actual quotient. Integrability follows from
an integrable periodization, so the seed need not have compact support. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPositive_unfold
    (f : CubicThetaPoint → ℝ) (hf : Measurable f) (hf0 : ∀ p,0≤f p)
    (g : CubicThetaQuotient → ℝ) (hg : Measurable g) (hg0 : ∀ q,0≤g q)
    (hgi : Integrable g cubicThetaQuotientMeasure)
    (hs : ∀ p,Summable (fun γ : cubicThetaPrincipalGroup => f (γ • p)))
    (he : ∀ p,(∑' γ : cubicThetaPrincipalGroup,f (γ • p))=g (cubicThetaQuotientMap p)) :
    Integrable f cubicThetaPointMeasure ∧
      (∫ p,f p ∂cubicThetaPointMeasure)=∫ q,g q ∂cubicThetaQuotientMeasure := by
  have hlin : (∫⁻ p,ENNReal.ofReal (f p) ∂cubicThetaPointMeasure)=
      ENNReal.ofReal (∫ q,g q ∂cubicThetaQuotientMeasure) := by
    calc
      _ = ∑' γ : cubicThetaPrincipalGroup,∫⁻ p in cubicThetaFundamentalDomain,
          ENNReal.ofReal (f (γ • p)) ∂cubicThetaPointMeasure :=
        (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).lintegral_eq_tsum'' _
      _ = ∫⁻ p in cubicThetaFundamentalDomain,
          ∑' γ : cubicThetaPrincipalGroup,ENNReal.ofReal (f (γ • p)) ∂cubicThetaPointMeasure := by
        rw [lintegral_tsum]
        intro γ
        exact (ENNReal.measurable_ofReal.comp (hf.comp (measurable_const_smul γ))).aemeasurable
      _ = ∫⁻ p in cubicThetaFundamentalDomain,
          ENNReal.ofReal (g (cubicThetaQuotientMap p)) ∂cubicThetaPointMeasure := by
        apply lintegral_congr
        intro p
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun γ => hf0 (γ • p)) (hs p),he p]
      _ = ∫⁻ q,ENNReal.ofReal (g q) ∂cubicThetaQuotientMeasure := by
        rw [cubicThetaQuotientMeasure]
        exact (lintegral_map (f:=fun q => ENNReal.ofReal (g q))
          (ENNReal.measurable_ofReal.comp hg)
          cubicThetaQuotientMap_open.continuous.measurable).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hgi
        (Filter.Eventually.of_forall hg0)).symm
  have hfi : Integrable f cubicThetaPointMeasure := by
    refine ⟨hf.aestronglyMeasurable,?_⟩
    change (∫⁻ p,‖f p‖ₑ ∂cubicThetaPointMeasure) < ⊤
    simp_rw [Real.enorm_of_nonneg (hf0 _)]
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)] at hlin
  have h := congrArg ENNReal.toReal hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hf0),
    ENNReal.toReal_ofReal (integral_nonneg hg0)] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarHeightSeed
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp scalar height cutoff has an actual half-open strip seed. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaScalarHeightWeight_nonneg {s v : ℝ} (hv : 0<v) :
    0 ≤ cubicThetaScalarHeightWeight s v := by
  unfold cubicThetaScalarHeightWeight
  split_ifs
  · exact Real.rpow_nonneg hv.le _
  · exact le_rfl

lemma cubicThetaScalarHeightSeed_nonneg (s : ℝ) (p : CubicThetaPoint) :
    0 ≤ cubicThetaScalarHeightSeed s p := by
  unfold cubicThetaScalarHeightSeed
  split_ifs
  · exact cubicThetaScalarHeightWeight_nonneg p.property
  · exact le_rfl

lemma cubicThetaScalarHeightSeed_translate (s : ℝ) (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation w • p)=
      if p.val.1+3*(w:ℂ)∈cubicThetaHorizontalCell then cubicThetaScalarHeightWeight s p.val.2 else 0 := by
  unfold cubicThetaScalarHeightSeed
  have h := cubicThetaPrincipalTranslation_coordinates w p
  change (cubicThetaPrincipalTranslation w • p).val=(p.val.1+3*(w:ℂ),p.val.2) at h
  rw [h]

lemma cubicThetaScalarHeightSeed_translation_hasSum (s : ℝ) (p : CubicThetaPoint) :
    HasSum (fun w : Eisenstein => cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation w • p))
      (cubicThetaScalarHeightWeight s p.val.2) := by
  obtain ⟨w,hw,huniq⟩ := cubicThetaHorizontalCell_unique_eisenstein p.val.1
  have hzero : ∀ v≠w,cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation v • p)=0 := by
    intro v hv
    rw [cubicThetaScalarHeightSeed_translate]
    exact ite_eq_right (fun hm => hv (huniq v hm))
  have h := hasSum_single w hzero
  rw [cubicThetaScalarHeightSeed_translate,ite_eq_left hw] at h
  exact h

lemma cubicThetaScalarHeightSeed_group_summable {s : ℝ} (hs : 2 < s) (p : CubicThetaPoint) :
    Summable (fun g : cubicThetaPrincipalGroup => cubicThetaScalarHeightSeed s (g • p)) := by
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  apply e.summable_iff.mp
  apply (summable_prod_of_nonneg (fun rw => cubicThetaScalarHeightSeed_nonneg s (e rw • p))).mpr
  constructor
  · intro r
    change Summable (fun w : Eisenstein => cubicThetaScalarHeightSeed s
      ((cubicThetaPrincipalTranslation w*r.completion) • p))
    simp_rw [mul_smul]
    exact (cubicThetaScalarHeightSeed_translation_hasSum s (r.completion • p)).summable
  · have hh (r : CubicThetaBottomRow) : (r.completion • p).val.2=r.height p.val := by
      change (cubicThetaBottomRow r.completion).height p.val=_
      rw [r.completion_row]
    change Summable (fun r : CubicThetaBottomRow => ∑' w : Eisenstein,
      cubicThetaScalarHeightSeed s ((cubicThetaPrincipalTranslation w*r.completion) • p))
    simp_rw [mul_smul,(cubicThetaScalarHeightSeed_translation_hasSum s _).tsum_eq,hh]
    exact cubicThetaScalarHeightCutoff_summable p.property hs

theorem cubicThetaScalarHeightSeed_group_sum {s : ℝ} (hs : 2 < s) (p : CubicThetaPoint) :
    (∑' g : cubicThetaPrincipalGroup,cubicThetaScalarHeightSeed s (g • p))=
      cubicThetaScalarHeightCutoff p.val s := by
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  let f : cubicThetaPrincipalGroup → ℝ := fun g => cubicThetaScalarHeightSeed s (g • p)
  have hsum := e.summable_iff.mpr (cubicThetaScalarHeightSeed_group_summable hs p)
  calc
    _ = ∑' rw : CubicThetaBottomRow × Eisenstein,f (e rw) := (e.tsum_eq f).symm
    _ = ∑' r : CubicThetaBottomRow,∑' w : Eisenstein,f (e (r,w)) := hsum.tsum_prod
    _ = ∑' r : CubicThetaBottomRow,cubicThetaScalarHeightWeight s (r.height p.val) := by
      apply tsum_congr
      intro r
      change (∑' w : Eisenstein,cubicThetaScalarHeightSeed s
        ((cubicThetaPrincipalTranslation w*r.completion) • p))=_
      simp_rw [mul_smul]
      rw [(cubicThetaScalarHeightSeed_translation_hasSum s _).tsum_eq]
      have hh : (r.completion • p).val.2=r.height p.val := by
        change (cubicThetaBottomRow r.completion).height p.val=_
        rw [r.completion_row]
      rw [hh]
    _ = _ := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarSeedPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact periodization of the positive sharp-height seed times section energy. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaScalarHeightWeight_measurable (s : ℝ) :
    Measurable (cubicThetaScalarHeightWeight s) := by
  unfold cubicThetaScalarHeightWeight
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · fun_prop
  · exact measurable_const

lemma cubicThetaScalarHeightSeed_measurable (s : ℝ) :
    Measurable (cubicThetaScalarHeightSeed s) := by
  apply Measurable.ite (cubicThetaHorizontalCell_measurable.preimage
    (measurable_fst.comp cubicThetaPointInclusion_measurableEmbedding.measurable))
  · exact (cubicThetaScalarHeightWeight_measurable s).comp
      (measurable_snd.comp cubicThetaPointInclusion_measurableEmbedding.measurable)
  · exact measurable_const

lemma cubicThetaSection_norm_invariant (F : CubicThetaSection)
    (γ : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    ‖F.val (γ • p)‖=‖F.val p‖ := by
  rw [F.property]
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaScalarRankinKernel_apply (σ : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarRankinKernel σ (cubicThetaQuotientMap p)=
      cubicThetaScalarHeightCutoff p.val (2+2*σ) := by
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨γ,hγ⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaScalarRankinKernel
  rw [←hγ]
  exact cubicThetaScalarHeightCutoff_invariant γ p.property _

lemma cubicThetaScalarEnergySeed_nonneg (F : CubicThetaSection) (σ : ℝ)
    (p : CubicThetaPoint) : 0 ≤ cubicThetaScalarEnergySeed F σ p :=
  mul_nonneg (cubicThetaScalarHeightSeed_nonneg _ p) (sq_nonneg _)

lemma cubicThetaScalarEnergyDensity_nonneg (F : CubicThetaSection) (σ : ℝ)
    (q : CubicThetaQuotient) : 0 ≤ cubicThetaScalarEnergyDensity F σ q :=
  mul_nonneg (cubicThetaScalarRankinKernel_nonneg σ q) (sq_nonneg _)

lemma cubicThetaScalarEnergySeed_measurable (F : CubicThetaSection) (σ : ℝ) :
    Measurable (cubicThetaScalarEnergySeed F σ) :=
  (cubicThetaScalarHeightSeed_measurable _).mul (F.val.continuous.norm.pow 2).measurable

lemma cubicThetaScalarEnergyDensity_measurable (F : CubicThetaSection) (σ : ℝ) :
    Measurable (cubicThetaScalarEnergyDensity F σ) :=
  (cubicThetaScalarRankinKernel_measurable σ).mul
    ((cubicThetaSectionRepresentative_measurable F).norm.pow_const 2)

lemma cubicThetaScalarEnergySeed_group_summable (F : CubicThetaSection)
    {σ : ℝ} (hσ : 0<σ) (p : CubicThetaPoint) :
    Summable (fun γ : cubicThetaPrincipalGroup => cubicThetaScalarEnergySeed F σ (γ • p)) := by
  simp only [cubicThetaScalarEnergySeed,cubicThetaSection_norm_invariant]
  exact (cubicThetaScalarHeightSeed_group_summable (by linarith) p).mul_right _

lemma cubicThetaScalarEnergySeed_group_sum (F : CubicThetaSection)
    {σ : ℝ} (hσ : 0<σ) (p : CubicThetaPoint) :
    (∑' γ : cubicThetaPrincipalGroup,cubicThetaScalarEnergySeed F σ (γ • p))=
      cubicThetaScalarEnergyDensity F σ (cubicThetaQuotientMap p) := by
  simp only [cubicThetaScalarEnergySeed,cubicThetaSection_norm_invariant]
  rw [tsum_mul_right,cubicThetaScalarHeightSeed_group_sum (by linarith)]
  unfold cubicThetaScalarEnergyDensity
  rw [cubicThetaScalarRankinKernel_apply]
  congr 1
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨γ,hγ⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change ‖F.val p‖^2=‖F.val (cubicThetaBorelSection (cubicThetaQuotientMap p))‖^2
  rw [←hγ,cubicThetaSection_norm_invariant]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRankinUnfold
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp Rankin kernel unfolds against the actual L2 model. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaScalarEnergyDensity_integrable
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    {σ K : ℝ} (hσ : 0<σ)
    (hb : ∀ q,‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖≤K) :
    Integrable (cubicThetaScalarEnergyDensity F σ) cubicThetaQuotientMeasure := by
  have hnorm : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := hF.integrable_norm_pow (by norm_num)
  apply (hnorm.const_mul (K/σ)).mono'
    (cubicThetaScalarEnergyDensity_measurable F σ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => by
    have hk := hb q
    have hn := cubicThetaScalarRankinKernel_nonneg σ q
    rw [←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hσ.le hn)] at hk
    have hdiv : cubicThetaScalarRankinKernel σ q≤K/σ := by
      apply (le_div_iff₀ hσ).mpr
      simpa only [mul_comm] using hk
    rw [Real.norm_of_nonneg (cubicThetaScalarEnergyDensity_nonneg F σ q)]
    exact mul_le_mul_of_nonneg_right hdiv (sq_nonneg _))

lemma cubicThetaScalarEnergySeed_unfold
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    {σ K : ℝ} (hσ : 0<σ)
    (hb : ∀ q,‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖≤K) :
    Integrable (cubicThetaScalarEnergySeed F σ) cubicThetaPointMeasure ∧
      (∫ p,cubicThetaScalarEnergySeed F σ p ∂cubicThetaPointMeasure)=
        ∫ q,cubicThetaScalarEnergyDensity F σ q ∂cubicThetaQuotientMeasure :=
  cubicThetaPositive_unfold _ (cubicThetaScalarEnergySeed_measurable F σ)
    (cubicThetaScalarEnergySeed_nonneg F σ) _ (cubicThetaScalarEnergyDensity_measurable F σ)
    (cubicThetaScalarEnergyDensity_nonneg F σ)
    (cubicThetaScalarEnergyDensity_integrable F hF hσ hb)
    (cubicThetaScalarEnergySeed_group_summable F hσ)
    (cubicThetaScalarEnergySeed_group_sum F hσ)

theorem cubicThetaArithmeticRankinMass_unfold_oai :
    ∀ᶠ σ : ℝ in 𝓝[>] 0,
      Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
        cubicThetaPointMeasure ∧
      cubicThetaArithmeticRankinMass σ=
        ∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
          ∂cubicThetaPointMeasure := by
  obtain ⟨K,_hK,hbound⟩ := cubicThetaScalarRankinKernel_uniform
  filter_upwards [hbound,self_mem_nhdsWithin] with σ hb hσ
  change 0<σ at hσ
  have hu := cubicThetaScalarEnergySeed_unfold cubicThetaArithmeticModelSection
    cubicThetaArithmeticModelGlobal_memLp hσ hb
  refine ⟨hu.1,?_⟩
  have hc := congrArg Complex.ofReal hu.2
  rw [←integral_complex_ofReal,←integral_complex_ofReal] at hc
  rw [hc,cubicThetaArithmeticRankinMass]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    dsimp only
    rw [cubicThetaArithmeticModelPairing_eq]
    simp only [cubicThetaScalarEnergyDensity,Complex.ofReal_mul,Complex.ofReal_pow])

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold_oai := @OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold_oai
