-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:27:07.006971+00:00
-- url     : https://prove2.me/submissions/82ab906c-ebdb-4a65-b6d3-f4658f946b9e

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Definitions.Def_OAIQ096A023

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerSeries
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Euler factors for the complete ideal Dirichlet series.
These retain the ramified factors lost in primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDirichlet_single_exclusion (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction {p} χ) idealExponentNorm s =
      (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))*
        normDirichletSeries χ idealExponentNorm s := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := if δ ≤ ν then f ν else 0
  have hf : Summable f := (idealDirichlet_norm_summable χ hχ hs).of_norm
  have hg : Summable g := by
    convert hf.indicator {ν | δ ≤ ν} using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    by_cases hν : δ ≤ ν <;> simp [g,Set.indicator,hν]
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hshift : (∑' ν, g ν)=f δ*(∑' ν, f ν) := by
    have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
      intro ν hν
      have hd : δ ≤ ν := by
        by_contra hn
        exact hν (by simp [g,hn])
      exact ⟨ν-δ,add_tsub_cancel_of_le hd⟩
    rw [←hi.tsum_eq hsup]
    simp only [g,le_add_of_nonneg_right zero_le,ite_true, if_true]
    simp_rw [show ∀ ν, f (δ+ν)=f δ*f ν from fun ν => idealDirichlet_weight_add χ hadd s δ ν]
    exact tsum_mul_left
  have he (ν : EisensteinIdealExponent) :
      primeIdealRestriction {p} χ ν*(idealExponentNorm ν:ℂ)^(-s)=f ν-g ν := by
    have hd : δ ≤ ν ↔ 0 < ν p := by
      simp only [δ,Finsupp.single_le_iff,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
    simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
    by_cases hp : ν p=0
    · simp [f,g,hd,hp]
    · simp [f,g,hd,hp,Nat.pos_of_ne_zero hp]
  unfold normDirichletSeries
  simp_rw [he]
  rw [hf.tsum_sub hg,hshift]
  dsimp only [f,δ]
  ring

end CubicFirstMoment

end

end OAI
end

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


lemma cubicThetaLatticeGaussianTail_nonneg (t : ℝ) :
    0 ≤ cubicThetaLatticeGaussianTail t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeightReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Properness of the actual arithmetic height denominator. Every point
has a maximal-height representative for the principal group. This is the
first reduction step for the global automorphic domain. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaBottomRow_height_superlevel_finite {p : ℂ × ℝ} (hp : 0<p.2)
    {a : ℝ} (ha : 0<a) :
    Set.Finite {r : CubicThetaBottomRow | a ≤ r.height p} := by
  let B := p.2*cubicThetaHeightConstant p/a
  have hfin : Set.Finite {r : CubicThetaBottomRow | norm r.c ≤ B ∧ norm r.d ≤ B} := by
    have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
      intro r t he
      exact CubicThetaBottomRow.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2
    exact ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  apply hfin.subset
  intro r hr
  have hN : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hmul : a*(1+norm r.c+norm r.d) ≤ p.2*cubicThetaHeightConstant p :=
    (le_div_iff₀ hN).mp (hr.trans (r.height_le hp))
  have hbound : 1+norm r.c+norm r.d ≤ B := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  exact ⟨by linarith [norm_nonneg r.d],by linarith [norm_nonneg r.c]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and factorization of the literal coefficient mass.
The unramified factors retain the primary and squarefree restrictions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryMass_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun d : PrimaryArgument => (norm d.val)^(-t)) :=
  (summable_eisenstein_norm_rpow ht).subtype _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticEulerFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed cubic Gauss series uses an actual primary coprimality
Euler factor. It is identified with a complete principal ideal series and
is nonzero throughout the half-plane needed for decompletion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_ideal_tsum (f : Eisenstein → ℂ) :
    (∑' ν : EisensteinIdealExponent, if primary (idealPrimaryGenerator ν) then
      f (idealPrimaryGenerator ν) else 0) = ∑' u : PrimaryArgument, f u := by
  let g (ν : EisensteinIdealExponent) : ℂ :=
    if primary (idealPrimaryGenerator ν) then f (idealPrimaryGenerator ν) else 0
  have hi : Function.Injective (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro a b h
    exact Subtype.ext (idealExponentOf_inj_primary a.property b.property h)
  have hs : Function.support g ⊆ Set.range (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro ν hν
    have hp : primary (idealPrimaryGenerator ν) := by
      by_contra hn
      exact hν (by simp [g,hn])
    exact ⟨⟨idealPrimaryGenerator ν,hp⟩,idealExponentOf_primaryGenerator ν⟩
  rw [←hi.tsum_eq hs]
  apply tsum_congr
  intro u
  simp [g,idealPrimaryGenerator_at_element u.property,u.property]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryMassEuler
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary norm series omits exactly the single ideal above three. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryGenerator_iff_unramified (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ν cubicThetaRamifiedPrime=0 := by
  constructor
  · intro hp
    apply Nat.eq_zero_of_not_pos
    intro hν
    have hd := (cubicThetaRamifiedPrime_dvd_iff ν).mpr hν
    have hd' : lambdaE ∣ idealPrimaryGenerator ν :=
      hd.trans (primaryNormalize_associated (idealExponentGenerator ν)).dvd
    exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hp).isRelPrime hd' dvd_rfl)
  · intro hν
    exact cubicThetaPrimaryGenerator_primary ⟨ν,hν⟩

lemma cubicThetaPrimaryMass_ideal (t : ℝ) :
    (cubicThetaPrimaryMass t:ℂ)=normDirichletSeries
      (primeIdealRestriction {cubicThetaRamifiedPrime} (fun _ => 1)) idealExponentNorm (t:ℂ) := by
  have h := primary_ideal_tsum (fun a => ((norm a)^(-t):ℝ))
  change (∑' ν, if primary (idealPrimaryGenerator ν) then
    (((norm (idealPrimaryGenerator ν))^(-t):ℝ):ℂ) else 0)=_ at h
  unfold cubicThetaPrimaryMass
  rw [Complex.ofReal_tsum,←h]
  unfold normDirichletSeries
  apply tsum_congr
  intro ν
  rw [cubicThetaPrimaryGenerator_iff_unramified,idealPrimaryGenerator_norm]
  simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
  split_ifs
  · rw [one_mul]
    simpa only [Complex.ofReal_neg] using Complex.ofReal_cpow (idealExponentNorm_pos ν).le (-t)
  · rw [zero_mul]

theorem cubicThetaPrimaryMass_euler {t : ℝ} (ht : 1 < t) :
    (cubicThetaPrimaryMass t:ℂ)=(1-(3:ℂ)^(-(t:ℂ)))*principalIdealZeta (t:ℂ) := by
  rw [cubicThetaPrimaryMass_ideal,idealDirichlet_single_exclusion _ _ (by simp)
    (by intros; simp) (by simpa using ht),←principalIdealZeta_right (by simpa using ht)]
  simp only [idealExponentNorm_single,pow_one,cubicThetaRamifiedPrime_norm,Nat.cast_ofNat,
    one_mul,Complex.ofReal_ofNat]

lemma cubicThetaPrimaryMass_pos {t : ℝ} (ht : 1 < t) : 0 < cubicThetaPrimaryMass t := by
  have h := (cubicThetaPrimaryMass_summable ht).le_tsum
    (⟨1,by norm_num [primary]⟩:PrimaryArgument)
    (fun d _ => Real.rpow_nonneg (norm_nonneg d.val) _)
  have he : (norm (1:Eisenstein))^(-t)=1 := by rw [norm_one_eq,Real.one_rpow]
  exact lt_of_lt_of_le (he ▸ zero_lt_one) h

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullLevelRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All level-three rows before the coprimality restriction. They form
one explicit affine lattice; primary common factors preserve the lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullRowMultiply_height (g : PrimaryArgument) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) :
    (cubicThetaFullRowMultiply g r).height p=(norm g.val)⁻¹*r.height p := by
  unfold CubicThetaFullRow.height CubicThetaBottomRow.height cubicThetaFullRowMultiply
  simp only [Subalgebra.coe_mul]
  rw [show (g.val:ℂ)*(r.c:ℂ)*p.1+(g.val:ℂ)*(r.d:ℂ)=
    (g.val:ℂ)*((r.c:ℂ)*p.1+r.d) by ring,Complex.normSq_mul]
  change p.2/(norm g.val*Complex.normSq ((r.c:ℂ)*p.1+r.d)+
    norm (g.val*r.c)*p.2^2)=_
  rw [norm_mul_eq]
  rw [show norm g.val*Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm g.val*norm r.c*p.2^2=
    norm g.val*(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2) by ring]
  rw [div_mul_eq_div_div]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarFactorization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of common primary factors from the scalar height series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullRowMultiply_rpow (g : PrimaryArgument) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    (cubicThetaFullRowMultiply g r).height p^s=(norm g.val)^(-s)*r.height p^s := by
  rw [cubicThetaFullRowMultiply_height,
    Real.mul_rpow (inv_nonneg.mpr (norm_nonneg _)) (r.height_pos hp).le,
    Real.inv_rpow (norm_nonneg _),←Real.rpow_neg (norm_nonneg _)]

lemma cubicThetaFullHeightMass_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) : Summable (fun r : CubicThetaFullRow => r.height p^s) := by
  have hg := cubicThetaPrimaryMass_summable (lt_trans (by norm_num) hs)
  have hr := cubicThetaScalarEisenstein_real_summable hp hs
  have hprod : Summable (fun z : PrimaryArgument × CubicThetaBottomRow =>
      (norm z.1.val)^(-s)*z.2.height p^s) :=
    summable_mul_of_summable_norm hg.norm hr.norm
  have ht : Summable (fun z : PrimaryArgument × CubicThetaBottomRow =>
      (cubicThetaPrimitiveRowEquiv z).height p^s) := hprod.congr
        (fun z => (cubicThetaFullRowMultiply_rpow z.1 z.2 hp s).symm)
  have hc := ht.comp_injective cubicThetaPrimitiveRowEquiv.symm.injective
  apply hc.congr
  intro r
  change (cubicThetaPrimitiveRowEquiv (cubicThetaPrimitiveRowEquiv.symm r)).height p^s=_
  rw [Equiv.apply_symm_apply]

theorem cubicThetaFullHeightMass_factorization {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    cubicThetaFullHeightMass p s=cubicThetaPrimaryMass s*cubicThetaScalarHeightMass p s := by
  have hg := cubicThetaPrimaryMass_summable (lt_trans (by norm_num) hs)
  have hr := cubicThetaScalarEisenstein_real_summable hp hs
  unfold cubicThetaFullHeightMass
  rw [←cubicThetaPrimitiveRowEquiv.tsum_eq (fun r => r.height p^s)]
  simp_rw [show ∀ z : PrimaryArgument × CubicThetaBottomRow,
      (cubicThetaPrimitiveRowEquiv z).height p^s=(norm z.1.val)^(-s)*z.2.height p^s from
    fun z => cubicThetaFullRowMultiply_rpow z.1 z.2 hp s]
  exact (summable_mul_of_summable_norm hg.norm hr.norm).tsum_prod.trans
    (by
      dsimp only
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
      rfl)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussian
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual affine four-dimensional Gaussian, before removal of common
primary factors. Its Mellin integral is the full height series. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaFullRow.denominator_pos (r : CubicThetaFullRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    0<Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
  by_cases hc : r.c=0
  · have hd := norm_pos_of_ne_zero (primary_ne_zero r.d_primary)
    simpa only [hc,Eisenstein.coe_zero,zero_mul,zero_add,norm,
      Complex.normSq_zero,mul_zero,add_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))

lemma CubicThetaFullRow.quadratic_pos (r : CubicThetaFullRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0 < r.quadratic p := div_pos (r.denominator_pos hp) hp

lemma CubicThetaFullRow.height_eq_inv (r : CubicThetaFullRow) (p : ℂ × ℝ) :
    r.height p=(r.quadratic p)⁻¹ := by
  simp only [CubicThetaFullRow.height,CubicThetaFullRow.quadratic,inv_div]

lemma cubicThetaFullGaussian_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    Summable (fun r : CubicThetaFullRow => Real.exp (-t*r.quadratic p)) := by
  have hs := cubicThetaFullHeightMass_summable hp (s:=3) (by norm_num)
  have hb := hs.mul_left (6/t^3)
  apply hb.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro r
  have hq := r.quadratic_pos hp
  have h := power_exp_bound ht 3 (r.quadratic p) hq.le
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,mul_one] at h
  rw [r.height_eq_inv,Real.rpow_ofNat,inv_pow]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hq 3)).mpr (by nlinarith [h])

lemma cubicThetaFullRowCoordinates_quadratic (a b : Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaFullRowCoordinates a b).quadratic p=
      Complex.normSq (3*(a:ℂ)*p.1+1+3*(b:ℂ))/p.2+9*norm a*p.2 := by
  unfold CubicThetaFullRow.quadratic cubicThetaFullRowCoordinates
  simp only [Subalgebra.coe_mul,Subalgebra.coe_add,Eisenstein.coe_one]
  change (Complex.normSq ((3:ℂ)*(a:ℂ)*p.1+(1+3*(b:ℂ)))+
    norm ((3:Eisenstein)*a)*p.2^2)/p.2=_
  rw [norm_mul_eq,show norm (3:Eisenstein)=9 by change Complex.normSq (3:ℂ)=9; norm_num]
  rw [show 3*(a:ℂ)*p.1+(1+3*(b:ℂ))=3*(a:ℂ)*p.1+1+3*(b:ℂ) by ring]
  field_simp

lemma cubicThetaFullGaussian_reindex {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    cubicThetaFullGaussian p t=∑' a : Eisenstein,
      Real.exp (-9*t*p.2*norm a)*cubicThetaScalarGaussianReal (3*(a:ℂ)*p.1+1) (t/p.2) := by
  have hs := (cubicThetaFullRowEquiv.summable_iff).mpr (cubicThetaFullGaussian_summable hp ht)
  unfold cubicThetaFullGaussian
  rw [←cubicThetaFullRowEquiv.tsum_eq]
  change Summable (fun c : Eisenstein × Eisenstein =>
    Real.exp (-t*(cubicThetaFullRowEquiv c).quadratic p)) at hs
  rw [hs.tsum_prod]
  apply tsum_congr
  intro a
  rw [cubicThetaScalarGaussianReal,←tsum_mul_left]
  apply tsum_congr
  intro b
  change Real.exp (-t*(cubicThetaFullRowCoordinates a b).quadratic p)=_
  rw [cubicThetaFullRowCoordinates_quadratic a b hp,←Real.exp_add]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianBound
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform control of the affine four-dimensional heat kernel by its
zero Fourier mode. Both errors come from explicit nonzero lattice vectors. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullGaussian_row_error {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    |cubicThetaFullGaussian p t-
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*cubicThetaScalarGaussianReal 0 (t*p.2)| ≤
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*
        cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))*
          cubicThetaScalarGaussianReal 0 (t*p.2) := by
  let E : Eisenstein → ℝ := fun a => Real.exp (-9*t*p.2*norm a)
  let G : Eisenstein → ℝ := fun a =>
    cubicThetaScalarGaussianReal (3*(a:ℂ)*p.1+1) (t/p.2)
  let K := 2*Real.pi/(9*Real.sqrt 3*(t/p.2))
  let T := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))
  have hK : 0≤K := by dsimp [K]; positivity
  have hT : 0≤T := cubicThetaLatticeGaussianTail_nonneg _
  have hE : Summable E := by
    convert cubicThetaScalarGaussianReal_summable 0 (mul_pos ht hp) using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    dsimp [E]
    congr 1
    ring
  have hEsum : ∑' a,E a=cubicThetaScalarGaussianReal 0 (t*p.2) := by
    unfold cubicThetaScalarGaussianReal
    apply tsum_congr
    intro a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    dsimp [E]
    congr 1
    ring
  have hG (a : Eisenstein) : 0≤G a := cubicThetaScalarGaussianReal_nonneg _ _
  have hGu (a : Eisenstein) : G a≤K*(1+T) :=
    cubicThetaScalarGaussianReal_le _ (div_pos ht hp)
  have hGe (a : Eisenstein) : |G a-K|≤K*T :=
    cubicThetaScalarGaussianReal_error _ (div_pos ht hp)
  have hF : Summable (fun a => E a*G a) := by
    apply (hE.mul_right (K*(1+T))).of_nonneg_of_le
    · intro a
      exact mul_nonneg (Real.exp_pos _).le (hG a)
    · intro a
      exact mul_le_mul_of_nonneg_left (hGu a) (Real.exp_pos _).le
  have hEK := hE.mul_right K
  have hD : Summable (fun a => E a*(G a-K)) := by
    simpa only [mul_sub] using hF.sub hEK
  have hmajor := hE.mul_right (K*T)
  rw [cubicThetaFullGaussian_reindex hp ht]
  change |(∑' a,E a*G a)-K*cubicThetaScalarGaussianReal 0 (t*p.2)|≤_
  rw [←hEsum,mul_comm K,←tsum_mul_right,←hF.tsum_sub hEK]
  calc
    _ = ‖∑' a,E a*(G a-K)‖ := by simp only [mul_sub,Real.norm_eq_abs]
    _ ≤ ∑' a,‖E a*(G a-K)‖ := norm_tsum_le_tsum_norm hD.norm
    _ ≤ ∑' a,E a*(K*T) := by
      apply hD.norm.tsum_le_tsum _ hmajor
      intro a
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hGe a) (Real.exp_pos _).le
    _ = _ := by rw [tsum_mul_right,hEsum]; ring

lemma cubicThetaFullGaussian_error {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    |cubicThetaFullGaussian p t-
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*(2*Real.pi/(9*Real.sqrt 3*(t*p.2)))| ≤
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*(2*Real.pi/(9*Real.sqrt 3*(t*p.2)))*
        (cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))*
          (1+cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2))))+
          cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))) := by
  let K := 2*Real.pi/(9*Real.sqrt 3*(t/p.2))
  let L := 2*Real.pi/(9*Real.sqrt 3*(t*p.2))
  let T := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))
  let U := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))
  let g := cubicThetaScalarGaussianReal 0 (t*p.2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hT : 0≤T := cubicThetaLatticeGaussianTail_nonneg _
  have he : |g-L|≤L*U := cubicThetaScalarGaussianReal_error 0 (mul_pos ht hp)
  have hg : g≤L*(1+U) := cubicThetaScalarGaussianReal_le 0 (mul_pos ht hp)
  have hr : |cubicThetaFullGaussian p t-K*g|≤K*T*g := cubicThetaFullGaussian_row_error hp ht
  change |cubicThetaFullGaussian p t-K*L|≤K*L*(T*(1+U)+U)
  calc
    _ = |(cubicThetaFullGaussian p t-K*g)+K*(g-L)| := by congr 1; ring
    _ ≤ |cubicThetaFullGaussian p t-K*g|+|K*(g-L)| := abs_add_le _ _
    _ ≤ K*T*g+K*(L*U) := by
      rw [abs_mul,abs_of_nonneg hK]
      exact add_le_add hr (mul_le_mul_of_nonneg_left he hK)
    _ ≤ K*T*(L*(1+U))+K*(L*U) :=
      add_le_add (mul_le_mul_of_nonneg_left hg (mul_nonneg hK hT)) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianLimit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading heat coefficient of the actual four-dimensional affine
lattice. The limit is independent of the upper-half-space point. -/
noncomputable section
open scoped Topology
open Filter
namespace CubicFirstMoment

lemma cubicThetaScalarGaussian_lead_product {v t : ℝ} (hv : 0<v) (ht : 0<t) :
    (2*Real.pi/(9*Real.sqrt 3*(t/v)))*(2*Real.pi/(9*Real.sqrt 3*(t*v)))=
      (4*Real.pi^2/243)/t^2 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3≠0 := by positivity
  field_simp
  nlinarith [hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin interchange for the literal affine row heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_2 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaFullRow : Countable CubicThetaFullRow := cubicThetaFullRowEquiv.symm.injective.countable

lemma cubicThetaFullGaussianMellinTerm_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaFullRow) :
    IntegrableOn (cubicThetaFullGaussianMellinTerm p s r) (Ioi 0) := by
  convert integrable_laplace_rpow hs (r.quadratic_pos hp) using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  unfold cubicThetaFullGaussianMellinTerm
  rw [show -t*r.quadratic p= -r.quadratic p*t by ring]

lemma cubicThetaFullGaussianMellinTerm_integral {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaFullRow) :
    (∫ t in Ioi (0:ℝ),cubicThetaFullGaussianMellinTerm p s r t)=
      Real.Gamma s*r.height p^s := by
  unfold cubicThetaFullGaussianMellinTerm
  simp_rw [show ∀ t : ℝ,-t*r.quadratic p= -r.quadratic p*t from fun t => by ring]
  rw [laplace_rpow hs (r.quadratic_pos hp),r.height_eq_inv,
    Real.inv_rpow (r.quadratic_pos hp).le,Real.rpow_neg (r.quadratic_pos hp).le]

lemma cubicThetaFullGaussianMellinTerm_mass {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0 < s) (r : CubicThetaFullRow) :
    (∫ t in Ioi (0:ℝ),‖cubicThetaFullGaussianMellinTerm p s r t‖)=
      Real.Gamma s*r.height p^s := by
  rw [←cubicThetaFullGaussianMellinTerm_integral hp hs r]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)

lemma cubicThetaFullGaussianMellin_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    Summable (fun r : CubicThetaFullRow =>
      ∫ t in Ioi (0:ℝ),‖cubicThetaFullGaussianMellinTerm p s r t‖) := by
  simp_rw [cubicThetaFullGaussianMellinTerm_mass hp (lt_trans (by norm_num) hs)]
  exact (cubicThetaFullHeightMass_summable hp hs).mul_left _

theorem cubicThetaFullGaussian_mellin {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaFullGaussian p t)=
      Real.Gamma s*cubicThetaFullHeightMass p s := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  calc
    _ = ∫ t in Ioi (0:ℝ),∑' r : CubicThetaFullRow,cubicThetaFullGaussianMellinTerm p s r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [cubicThetaFullGaussian,←tsum_mul_left]
      rfl
    _ = ∑' r : CubicThetaFullRow,∫ t in Ioi (0:ℝ),cubicThetaFullGaussianMellinTerm p s r t :=
      (integral_tsum_of_summable_integral_norm
        (fun r => cubicThetaFullGaussianMellinTerm_integrable hp hs0 r)
        (cubicThetaFullGaussianMellin_summable hp hs)).symm
    _ = _ := by
      simp_rw [cubicThetaFullGaussianMellinTerm_integral hp hs0]
      rw [tsum_mul_left]
      rfl

lemma cubicThetaFullGaussian_mellin_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) (Ioi 0) := by
  have hm := cubicThetaFullGaussian_mellin hp hs
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hmass : 0 < cubicThetaFullHeightMass p s := by
    let r := cubicThetaFullRowCoordinates 0 0
    have hp' : 0 < r.height p := by rw [r.height_eq_inv]; exact inv_pos.mpr (r.quadratic_pos hp)
    have hq (q : CubicThetaFullRow) : 0≤q.height p := by
      rw [q.height_eq_inv]
      exact inv_nonneg.mpr (q.quadratic_pos hp).le
    exact (Real.rpow_pos_of_pos hp' s).trans_le
      ((cubicThetaFullHeightMass_summable hp hs).le_tsum r
        (fun q _ => Real.rpow_nonneg (hq q) s))
  by_contra hn
  rw [integral_undef hn] at hm
  exact (ne_of_gt (mul_pos (Real.Gamma_pos_of_pos hs0) hmass)) hm.symm

lemma cubicThetaFullGaussian_measurable (p : ℂ × ℝ) :
    Measurable (cubicThetaFullGaussian p) := by
  apply Measurable.tsum
  intro r
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded remainder after subtracting the exact leading heat term. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaFullGaussian_bounded_remainder {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, 0<t → t≤1 →
      |cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2|≤M := by
  let C := 4*Real.pi^2/243
  let a := 4*Real.pi^2*p.2/27
  let b := 4*Real.pi^2/(27*p.2)
  let A := cubicThetaGaussianPowerConstant/a^2
  let B := cubicThetaGaussianPowerConstant/b^2
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hA : 0≤A := div_nonneg cubicThetaGaussianPowerConstant_nonneg (sq_nonneg _)
  have hB : 0≤B := div_nonneg cubicThetaGaussianPowerConstant_nonneg (sq_nonneg _)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C*(A*(1+B)+B),by positivity,?_⟩
  intro t ht ht1
  have hT : cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))≤A*t^2 := by
    have h := cubicThetaLatticeGaussianTail_div_bound ha ht
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [a]
    congr 1
    field_simp
  have hU : cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))≤B*t^2 := by
    have h := cubicThetaLatticeGaussianTail_div_bound hb ht
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [b]
    congr 1
    ring
  have he := cubicThetaFullGaussian_error hp ht
  rw [cubicThetaScalarGaussian_lead_product hp ht] at he
  calc
    _ ≤ C/t^2*(A*t^2*(1+B*t^2)+B*t^2) := he.trans (by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hC (sq_nonneg t))
      exact add_le_add (mul_le_mul hT (add_le_add le_rfl hU)
        (by linarith [cubicThetaLatticeGaussianTail_nonneg (4*Real.pi^2/(27*(t*p.2)))]) (mul_nonneg hA (sq_nonneg t))) hU)
    _ = C*(A*(1+B*t^2)+B) := by field_simp [ht.ne']
    _ ≤ C*(A*(1+B)+B) := by
      have ht2 : t^2≤1 := by nlinarith
      have hbt : B*t^2≤B := by nlinarith [mul_nonneg hB (sub_nonneg.mpr ht2)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbt) hA) le_rfl) hC

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularHeatHigh
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-time Mellin integral is continuous at the critical exponent,
with domination supplied by the proved height mass at exponent three. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaFullGaussian_nonneg (p : ℂ × ℝ) (t : ℝ) :
    0 ≤ cubicThetaFullGaussian p t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma cubicThetaRegularHeatHigh_bound {p : ℂ × ℝ} {s t : ℝ}
    (hs : s ≤ 3) (ht : 1<t) :
    ‖t^(s-1)*cubicThetaFullGaussian p t‖ ≤ t^(3-1:ℝ)*cubicThetaFullGaussian p t := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (cubicThetaFullGaussian_nonneg p t))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (cubicThetaFullGaussian_nonneg p t)

theorem cubicThetaRegularHeatHigh_integral_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaFullGaussian p t)
      (𝓝[>] 2) (𝓝 (∫ t in Ioi (1:ℝ),t^(2-1:ℝ)*cubicThetaFullGaussian p t)) := by
  have h3 := (cubicThetaFullGaussian_mellin_integrable hp (s:=3) (by norm_num)).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => t^(3-1:ℝ)*cubicThetaFullGaussian p t) ?_ ?_ h3 ?_
  · exact Filter.Eventually.of_forall (fun s => by
      have hF := cubicThetaFullGaussian_measurable p
      apply Measurable.aestronglyMeasurable
      fun_prop)
  · have he : ∀ᶠ s : ℝ in 𝓝[>] 2,s<3 :=
      (show ∀ᶠ s : ℝ in 𝓝 2,s<3 from Iio_mem_nhds (by norm_num : (2:ℝ)<3)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaRegularHeatHigh_bound hs.le ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1<t at ht
    have hc : ContinuousAt (fun s : ℝ => t^(s-1)) 2 :=
      (Real.continuousAt_const_rpow (by linarith : t≠0)).comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularHeatLow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-time Mellin remainder is integrable and continuous at the
critical exponent after subtracting the proved heat coefficient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRegularHeatLow_measurable (p : ℂ × ℝ) (s : ℝ) :
    Measurable (cubicThetaRegularHeatLow p s) := by
  have hF := cubicThetaFullGaussian_measurable p
  unfold cubicThetaRegularHeatLow
  fun_prop

lemma cubicThetaRegularHeatLow_bound {p : ℂ × ℝ} {M s t : ℝ}
    (hM : 0 ≤ M) (hbound : |cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2| ≤ M)
    (hs : 2 ≤ s) (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖cubicThetaRegularHeatLow p s t‖ ≤ M*t := by
  have hp : t^(s-1) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
      (show (1:ℝ) ≤ s-1 by linarith)
  rw [cubicThetaRegularHeatLow,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ht.1.le _)).trans
    (by nlinarith)

theorem cubicThetaRegularHeatLow_integral_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)
      (𝓝[>] 2) (𝓝 (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p 2 t)) := by
  obtain ⟨M,hM,hbound⟩ := cubicThetaFullGaussian_bounded_remainder hp
  have hi : IntegrableOn (fun t : ℝ => M*t) (Ioc 0 1) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => M*t) ?_ ?_ hi ?_
  · exact Filter.Eventually.of_forall (fun s => (cubicThetaRegularHeatLow_measurable p s).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact cubicThetaRegularHeatLow_bound hM (hbound t ht.1 ht.2) hs.le ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hc : ContinuousAt (fun s : ℝ => t^(s-1)) 2 :=
      (Real.continuousAt_const_rpow ht.1.ne').comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

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

lemma cubicThetaRegularHeatMass_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (cubicThetaRegularHeatMass p) (𝓝[>] 2) (𝓝 (cubicThetaRegularHeatMass p 2)) :=
  (cubicThetaRegularHeatLow_integral_tendsto hp).add
    (cubicThetaRegularHeatHigh_integral_tendsto hp)

lemma cubicThetaHeatPole_integral {s : ℝ} (hs : 2 < s) :
    (∫ t in Ioc (0:ℝ) 1,t^(s-3))=1/(s-2) := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1 < s-3))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : s-3+1≠0)]
  congr 1 <;> ring

lemma cubicThetaRegularHeatLow_integral_eq {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)=
      (∫ t in Ioc (0:ℝ) 1,t^(s-1)*cubicThetaFullGaussian p t)-
        (4*Real.pi^2/243)/(s-2) := by
  have hf : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) (Ioc 0 1) :=
    (cubicThetaFullGaussian_mellin_integrable hp hs).mono_set Ioc_subset_Ioi_self
  have hg : IntegrableOn (fun t : ℝ => (4*Real.pi^2/243)*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s-3))).const_mul _
  have he : ∀ t∈Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t=
      t^(s-1)*cubicThetaFullGaussian p t-(4*Real.pi^2/243)*t^(s-3) := by
    intro t ht
    have ht0 := ht.1
    unfold cubicThetaRegularHeatLow
    have hpow : t^(s-1)/t^2=t^(s-3) := by
      rw [←Real.rpow_two,←Real.rpow_sub ht0]
      congr 1
      ring
    rw [mul_sub]
    congr 1
    calc
      _ = (4*Real.pi^2/243)*(t^(s-1)/t^2) := by ring
      _ = _ := by rw [hpow]
  rw [setIntegral_congr_fun measurableSet_Ioc he,integral_sub hf hg,
    integral_const_mul,cubicThetaHeatPole_integral hs]
  ring

theorem cubicThetaFullHeightMass_pole_identity {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    Real.Gamma s*cubicThetaFullHeightMass p s=
      (4*Real.pi^2/243)/(s-2)+cubicThetaRegularHeatMass p s := by
  rw [←cubicThetaFullGaussian_mellin hp hs,←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((cubicThetaFullGaussian_mellin_integrable hp hs).mono_set Ioc_subset_Ioi_self)
      ((cubicThetaFullGaussian_mellin_integrable hp hs).mono_set
        (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)))]
  rw [cubicThetaRegularHeatMass,cubicThetaRegularHeatLow_integral_eq hp hs]
  ring

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

lemma cubicThetaRealGamma_two : Real.Gamma 2=1 := by
  norm_num

theorem cubicThetaFullHeightMass_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => (s-2)*cubicThetaFullHeightMass p s) (𝓝[>] 2)
      (𝓝 (4*Real.pi^2/243)) := by
  let C := 4*Real.pi^2/243
  have hzero : Tendsto (fun s : ℝ => s-2) (𝓝[>] 2) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℝ => s-2) 2 := by fun_prop
    simpa only [sub_self] using h.tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hR := cubicThetaRegularHeatMass_tendsto hp
  have hnum : Tendsto (fun s : ℝ => C+(s-2)*cubicThetaRegularHeatMass p s)
      (𝓝[>] 2) (𝓝 C) := by
    simpa using tendsto_const_nhds.add (hzero.mul hR)
  have hG : Tendsto Real.Gamma (𝓝[>] (2:ℝ)) (𝓝 1) := by
    simpa only [cubicThetaRealGamma_two] using
      cubicThetaRealGamma_continuousAt_two.tendsto.mono_left nhdsWithin_le_nhds
  have hd := hnum.div hG (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 2 < s at hs
  have he := cubicThetaFullHeightMass_pole_identity hp hs
  have hGamma := (Real.Gamma_pos_of_pos (lt_trans (by norm_num) hs)).ne'
  apply (div_eq_iff hGamma).mpr
  have hne : s-2≠0 := by linarith
  dsimp [C]
  field_simp [hne] at he
  nlinarith [he]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarResidueReduction
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the regular primary common-factor series at the scalar pole. -/
noncomputable section
open scoped Topology
open Filter
namespace CubicFirstMoment

lemma cubicThetaPrimaryMass_continuousOn :
    ContinuousOn cubicThetaPrimaryMass (Set.Ioi 1) := by
  intro t ht
  change 1<t at ht
  let a := (1+t)/2
  have ha : 1<a := by dsimp [a]; linarith
  have hat : a<t := by dsimp [a]; linarith
  have hc : ContinuousOn cubicThetaPrimaryMass (Set.Ici a) := by
    have hf (d : PrimaryArgument) : Continuous (fun u : ℝ => (norm d.val)^(-u)) :=
      (Real.continuous_const_rpow (norm_pos_of_ne_zero
        (primary_ne_zero d.property)).ne').comp continuous_neg
    apply continuousOn_tsum (fun d => (hf d).continuousOn) (cubicThetaPrimaryMass_summable ha)
    intro d u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero d.property))
      (neg_le_neg hu)
  exact (hc.continuousAt (Ici_mem_nhds hat)).continuousWithinAt

lemma cubicThetaPrimaryMass_two :
    (cubicThetaPrimaryMass 2:ℂ)=(8/9:ℂ)*principalIdealZeta 2 := by
  rw [cubicThetaPrimaryMass_euler (by norm_num)]
  congr 1
  norm_num [Complex.cpow_ofNat,Complex.cpow_neg]

lemma cubicThetaScalarEisenstein_ofReal {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    cubicThetaScalarEisenstein p (s:ℂ)=(cubicThetaScalarHeightMass p s:ℂ) := by
  rw [cubicThetaScalarEisenstein,cubicThetaScalarHeightMass,Complex.ofReal_tsum]
  apply tsum_congr
  intro r
  exact (Complex.ofReal_cpow (r.height_pos hp).le s).symm

lemma cubicThetaScalarHeightMass_eq_div {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    cubicThetaScalarHeightMass p s=cubicThetaFullHeightMass p s/cubicThetaPrimaryMass s := by
  rw [cubicThetaFullHeightMass_factorization hp hs]
  field_simp [(cubicThetaPrimaryMass_pos (lt_trans (by norm_num) hs)).ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar Eisenstein residue at two, computed from the affine
lattice and the exact primary common-factor Euler product. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaScalarEisenstein_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)*cubicThetaScalarEisenstein p (s:ℂ))
      (𝓝[>] 2) (𝓝 ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (cubicThetaFullHeightMass_residue hp)
  have hpcont := (cubicThetaPrimaryMass_continuousOn.continuousAt
    (Ioi_mem_nhds (by norm_num : (1:ℝ)<2))).tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hpC := Complex.continuous_ofReal.continuousAt.tendsto.comp hpcont
  have hp0 : (cubicThetaPrimaryMass 2:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaPrimaryMass_pos (by norm_num)).ne'
  have hd := hf.div hpC hp0
  have hval : ((4*Real.pi^2/243:ℝ):ℂ)/(cubicThetaPrimaryMass 2:ℂ)=
      (Real.pi:ℂ)^2/(54*principalIdealZeta 2) := by
    rw [cubicThetaPrimaryMass_two]
    push_cast
    ring
  rw [hval] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 2 < s at hs
  change (((s-2)*cubicThetaFullHeightMass p s:ℝ):ℂ)/(cubicThetaPrimaryMass s:ℂ)=_
  rw [cubicThetaScalarEisenstein_ofReal hp,cubicThetaScalarHeightMass_eq_div hp hs]
  push_cast
  ring

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

lemma cubicThetaScalarHeightHigh_continuous {p : ℂ × ℝ} (hp : 0<p.2) :
    Continuous (cubicThetaScalarHeightHigh p) := by
  classical
  let S := (cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).toFinset
  have he (s : ℝ) : cubicThetaScalarHeightHigh p s=
      ∑ r∈S,if 1 < r.height p then r.height p^s else 0 := by
    apply tsum_eq_sum
    intro r hr
    have hn : ¬1 < r.height p := by
      intro hh
      exact hr (by change r∈(cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).toFinset
                   simpa using hh.le)
    simp only [ite_eq_right hn]
  rw [show cubicThetaScalarHeightHigh p=(fun s => ∑ r∈S,if 1 < r.height p then r.height p^s else 0) from funext he]
  apply continuous_finsetSum
  intro r _
  by_cases hr : 1 < r.height p
  · simp only [ite_eq_left hr]
    exact Real.continuous_const_rpow (r.height_pos hp).ne'
  · simp only [ite_eq_right hr]
    exact continuous_const

lemma cubicThetaScalarHeightHigh_summable {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    Summable (fun r : CubicThetaBottomRow => if 1 < r.height p then r.height p^s else 0) := by
  apply summable_of_hasFiniteSupport
  apply (cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).subset
  intro r hr
  have hpos : 1 < r.height p := by
    by_contra hn
    exact hr (ite_eq_right hn)
  exact hpos.le

lemma cubicThetaScalarHeightCutoff_split {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 < s) :
    cubicThetaScalarHeightMass p s=
      cubicThetaScalarHeightCutoff p s+cubicThetaScalarHeightHigh p s := by
  rw [cubicThetaScalarHeightCutoff,cubicThetaScalarHeightHigh,
    ←(cubicThetaScalarHeightCutoff_summable hp hs).tsum_add
      (cubicThetaScalarHeightHigh_summable hp s)]
  apply tsum_congr
  intro r
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr,ite_eq_right (not_lt.mpr hr),add_zero]
  · simp only [ite_eq_right hr,ite_eq_left (lt_of_not_ge hr),zero_add]

theorem cubicThetaScalarHeightCutoff_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)*(cubicThetaScalarHeightCutoff p s:ℂ))
      (𝓝[>] 2) (𝓝 ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
  have hzero : Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)) (𝓝[>] 2) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℝ => ((s-2:ℝ):ℂ)) 2 := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using h.tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hH := (Complex.continuous_ofReal.comp (cubicThetaScalarHeightHigh_continuous hp)).continuousAt.tendsto.mono_left
    (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have h := (cubicThetaScalarEisenstein_residue hp).sub (hzero.mul hH)
  simp only [zero_mul,sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [cubicThetaScalarEisenstein_ofReal hp,cubicThetaScalarHeightCutoff_split hp hs]
  dsimp only [Function.comp_apply]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

theorem cubicThetaScalarRankinKernel_residue (q : CubicThetaQuotient) :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ))
      (𝓝[>] 0) (𝓝 ((Real.pi:ℂ)^2/(108*principalIdealZeta 2))) := by
  have hpath : Tendsto (fun σ : ℝ => 2+2*σ) (𝓝[>] 0) (𝓝[>] 2) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun σ : ℝ => 2+2*σ) 0 := by fun_prop
      simpa using h.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change 0<σ at hσ
      change 2<2+2*σ
      linarith
  have h := ((cubicThetaScalarHeightCutoff_residue (cubicThetaBorelSection q).property).comp hpath).const_mul (1/2:ℂ)
  convert h using 1
  · funext σ
    dsimp only [Function.comp_apply,cubicThetaScalarRankinKernel]
    push_cast
    ring
  · congr 1
    ring

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

theorem cubicThetaScalarRankinKernel_integral_limit_oai
    (F : CubicThetaQuotient → ℂ) (hF : Integrable F cubicThetaQuotientMeasure) :
    Tendsto (fun σ : ℝ => ∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*F q
        ∂cubicThetaQuotientMeasure) (𝓝[>] 0)
      (𝓝 (((Real.pi:ℂ)^2/(108*principalIdealZeta 2))*
        ∫ q,F q ∂cubicThetaQuotientMeasure)) := by
  obtain ⟨K,hK,hbound⟩ := cubicThetaScalarRankinKernel_uniform
  rw [←integral_const_mul]
  apply tendsto_integral_filter_of_dominated_convergence (fun q => K*‖F q‖)
  · apply Filter.Eventually.of_forall
    intro σ
    have hm : Measurable (fun q => (σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)) := by
      exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (cubicThetaScalarRankinKernel_measurable σ))
    exact hm.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · filter_upwards [hbound] with σ hσ
    exact Filter.Eventually.of_forall (fun q => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hσ q) (_root_.norm_nonneg _))
  · exact hF.norm.const_mul K
  · exact Filter.Eventually.of_forall (fun q =>
      (cubicThetaScalarRankinKernel_residue q).mul tendsto_const_nhds)

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit_oai := @OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit_oai
