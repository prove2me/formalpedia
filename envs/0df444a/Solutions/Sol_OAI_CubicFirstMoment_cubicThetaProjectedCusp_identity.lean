-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:16:08.420653+00:00
-- url     : https://prove2.me/submissions/8edb6ee5-f810-4532-8522-8ddc38f92580

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second finite character needed at the ramified place: the unit
omega, restricted to primary numerators. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaUnitCharacter_coordinates (a b : ℤ) :
    cubicThetaUnitCharacter ((a:Eisenstein)+b*omegaE)=omega^(2*(a+b)) := by
  rw [AddChar.map_add_eq_mul]
  have ha : cubicThetaUnitCharacter (a:Eisenstein)=(omega^2)^a := by
    rw [show (a:Eisenstein)=a • (1:Eisenstein) by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaUnitCharacter_one]
  have hb : cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)=(omega^2)^b := by
    rw [show (b:Eisenstein)*omegaE=b • omegaE by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaUnitCharacter_omega]
  rw [ha,hb,← zpow_add₀ (pow_ne_zero 2 (omega_primitive.ne_zero (by decide)))]
  rw [← zpow_natCast omega 2,← zpow_mul]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryUnitTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the six primary-series unit twists into the actual frequency.
This keeps the ramified residue equations on one finite unit orbit. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimaryFourierSeries_two_shift (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries 1 2 s h=
      cubicThetaPrimaryFourierSeries 1 1 s (lambdaE*h) := by
  simpa only [pow_one] using (cubicThetaPrimaryFourierSeries_lambda_pow 1 1 1 s h).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual common nonconstant coefficient is nonzero. Otherwise
global automorphy would force a pure height power to be invariant. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_ne_zero : cubicThetaArithmeticBaseScalar≠0 := by
  intro hB
  let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
  let g₀ : SL(2,Eisenstein) := ⟨!![1,0;3,1],by simp [Matrix.det_fin_two]⟩
  have hg : g₀∈cubicThetaPrincipalGroup :=
    (cubicThetaPrincipalGroup_mem_iff g₀).mpr
      ⟨primary_one,dvd_zero _,dvd_refl _,primary_one⟩
  let g : cubicThetaPrincipalGroup := ⟨g₀,hg⟩
  have hp : (g • p).val.2=(1/10:ℝ) := by
    change (cubicThetaMobius (cubicThetaPrincipalComplex g) (0,1)).2=(1/10:ℝ)
    norm_num [cubicThetaMobius,cubicThetaMobiusDenominator,
      cubicThetaPrincipalComplex_apply,g,g₀]
    change (1+Complex.normSq (3:ℂ))⁻¹=(1/10:ℝ)
    norm_num [Complex.normSq_apply]
  have hC : 0 < cubicThetaConstant := by unfold cubicThetaConstant; positivity
  have hnorm (q : CubicThetaPoint) :
      ‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar q.val‖=
        cubicThetaConstant*q.val.2^(2/3:ℝ) := by
    rw [cubicThetaArithmeticModel,hB,zero_mul,add_zero,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (mul_pos hC (Real.rpow_pos_of_pos q.property _))]
  have he := congrArg (fun z : ℂ => ‖z‖) (cubicThetaArithmeticModel_automorphy g p)
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul,hnorm,hnorm,hp] at he
  change cubicThetaConstant*(1/10:ℝ)^(2/3:ℝ)=cubicThetaConstant*1^(2/3:ℝ) at he
  have hlt : (1/10:ℝ)^(2/3:ℝ)<1 := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ)≤1/10)
      (by norm_num : (1/10:ℝ)<1) (by norm_num : (0:ℝ)<2/3)
  rw [Real.one_rpow] at he
  have he' := (mul_left_cancel₀ hC.ne' he)
  exact (ne_of_lt hlt) he'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelPullback
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null sets on the arithmetic quotient lift to null sets upstairs.
The countable translates of positive strips supply the required exhaustion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

theorem cubicThetaQuotient_pull_ae {P : CubicThetaQuotient → Prop}
    (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure,P (cubicThetaQuotientMap p) := by
  have hs (n : ℕ) : ∀ᵐ p ∂cubicThetaPointMeasure,
      p∈cubicThetaCuspStrip (1/(n+1:ℝ)) → P (cubicThetaQuotientMap p) :=
    (ae_restrict_iff' (cubicThetaCuspStrip_measurable _)).mp
      (cubicThetaPositiveStrip_pull_ae (by positivity) hP)
  have hall : ∀ᵐ p ∂cubicThetaPointMeasure,∀ w : Eisenstein,∀ n : ℕ,
      cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
        P (cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • p)) :=
    ae_all_iff.mpr (fun w => ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (cubicThetaPrincipalTranslation w)
        cubicThetaPointMeasure).quasiMeasurePreserving.ae (hs n)))
  filter_upwards [hall] with p hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt p.property
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hn
  simpa only [cubicThetaQuotient_covering.map_smul] using hp w n hw

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inversion operator on quotient representatives, including
the cubic phase of the chosen Borel section. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversionFunction_lift (f : CubicThetaQuotient → ℂ)
    (p : CubicThetaPoint) :
    cubicThetaBorelLift (cubicThetaBorelInversionFunction f) p=
      cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelLift,cubicThetaBorelPhase_sheet g hg,cubicThetaBorelInversionFunction,
    ←cubicThetaInversionConjugate_character g,←cubicThetaBorelLift_automorphy,
    ←cubicThetaInversion_intertwine]
  exact congrArg (fun x => cubicThetaBorelLift f (cubicThetaFullInversion • x)) hg

theorem cubicThetaBorelInversion_lift (f : CubicThetaGlobalL2) :
    cubicThetaBorelLift (cubicThetaBorelInversion f)
      =ᵐ[cubicThetaPointMeasure] fun p => cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  filter_upwards [cubicThetaQuotient_pull_ae
    (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp] with p hp
  change ((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_ at hp
  change cubicThetaBorelPhase p*((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_
  rw [hp]
  exact cubicThetaBorelInversionFunction_lift f p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inversion symmetry of the actual residual vector holds
pointwise for its continuous arithmetic Fourier expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversion_smooth (F : cubicThetaSmoothTests) :
    cubicThetaBorelInversion (cubicThetaGlobalMass F)=
      cubicThetaGlobalMass (cubicThetaInversionSmooth F) := by
  apply Lp.ext
  have hcomp := (cubicThetaIntegralQuotient_measurePreserving
    cubicThetaFullInversion).quasiMeasurePreserving.ae
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp
  filter_upwards [(cubicThetaBorelInversionFunction_memLp
    (cubicThetaGlobalMass F)).coeFn_toLp,
    (cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).coeFn_toLp,
    hcomp] with q hT hI hF
  change ((cubicThetaBorelInversionFunction_memLp (cubicThetaGlobalMass F)).toLp _) q=
    ((cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).toLp _) q
  rw [hT,hI]
  unfold cubicThetaBorelInversionFunction
  change cubicThetaBorelPhase (cubicThetaFullInversion • cubicThetaBorelSection q)*
    (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
        F.val.val (cubicThetaFullInversion • cubicThetaBorelSection q)
  have he : (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
      cubicThetaSectionRepresentative F (cubicThetaQuotientMap
        (cubicThetaFullInversion • cubicThetaBorelSection q)) := by
    change (cubicThetaGlobalMass F) (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)=
      cubicThetaSectionRepresentative F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) at hF
    simpa only [←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
      using hF
  rw [he]
  exact cubicThetaBorelLift_section F (cubicThetaFullInversion • cubicThetaBorelSection q)

theorem cubicThetaBorelInversion_energy (u : cubicThetaGlobalEnergySpace) :
    cubicThetaBorelInversion (cubicThetaGlobalInclusion u)=
      cubicThetaGlobalInclusion (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaBorelInversion.continuous.comp cubicThetaGlobalInclusion.continuous)
      (cubicThetaGlobalInclusion.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  intro F
  change cubicThetaBorelInversion (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F))=
    cubicThetaGlobalInclusion (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F))
  rw [cubicThetaInversionEnergy_test,cubicThetaGlobalInclusion_test,
    cubicThetaGlobalInclusion_test,cubicThetaBorelInversion_smooth]

theorem cubicThetaNormalizedArithmeticResidue_inversion :
    cubicThetaInversionEnergy cubicThetaNormalizedArithmeticResidue=
      cubicThetaNormalizedArithmeticResidue := by
  unfold cubicThetaNormalizedArithmeticResidue
  rw [map_smul,cubicThetaArithmeticResidueEnergy_inversion]

theorem cubicThetaArithmeticModel_inversion (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have hT := cubicThetaBorelInversion_lift
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
  rw [cubicThetaBorelInversion_energy,cubicThetaNormalizedArithmeticResidue_inversion] at hT
  have hcomp := (measurePreserving_smul cubicThetaFullInversion
    cubicThetaPointMeasure).quasiMeasurePreserving.ae cubicThetaArithmeticModel_global_ae
  have he : (fun p : CubicThetaPoint => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaFullInversion • p).val)=ᵐ[cubicThetaPointMeasure]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae,hcomp,hT] with q hq hSq hIq
    exact hSq.symm.trans (hIq.symm.trans hq)
  have hc := cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar
  exact congrFun (Measure.eq_of_ae_eq he
    (hc.comp (continuous_const_smul cubicThetaFullInversion)) hc) p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaContinuousFourierSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual periodic continuous functions are determined by their cell coefficients. -/
noncomputable section
open Set MeasureTheory Filter
namespace CubicFirstMoment

local instance localInst_rda9fe9_1 : Countable Eisenstein := cubicThetaFourierIndex.injective.countable
theorem cubicThetaContinuousFourier_ext {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ (m : Eisenstein) z,f (z+3*(m:ℂ))=f z)
    (hgp : ∀ (m : Eisenstein) z,g (z+3*(m:ℂ))=g z)
    (he : ∀ h : Eisenstein,
      (∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=
      ∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*g z) : f=g := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) :=
    isFiniteMeasure_restrict.mpr cubicThetaHorizontalCell_measure_ne_top
  have hD : MemLp (fun z => f z-g z) 2
      ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) := by
    obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn (hf.sub hg).continuousOn
    apply MemLp.of_bound (hf.sub hg).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem cubicThetaHorizontalCell_measurable] with z hz
    exact hC z (hcell hz)
  have hphase (h : Eisenstein) : Continuous (fun z : ℂ =>
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)) := by
    have hc : Continuous (fun z : ℂ => Real.fourierChar (tracePair z (cubicThetaRowFrequency h))) :=
      Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
    exact (continuous_subtype_val.comp hc).star
  have hi (h : Eisenstein) (F : ℂ → ℂ) (hF : Continuous F) :
      IntegrableOn (fun z => star (Real.fourierChar
        (tracePair z (cubicThetaRowFrequency h)):ℂ)*F z) cubicThetaHorizontalCell :=
    (((hphase h).mul hF).continuousOn.integrableOn_compact hL).mono_set hcell
  have hcellzero := cubicThetaCellFourier_separates hD (fun h => by
    simp_rw [mul_sub]
    rw [integral_sub (hi h f hf) (hi h g hg),he h,sub_self])
  have hcell' : ∀ᵐ z ∂(volume : Measure ℂ),z∈cubicThetaHorizontalCell → f z=g z := by
    have ht := (ae_restrict_iff' cubicThetaHorizontalCell_measurable).mp hcellzero
    filter_upwards [ht] with z hz hmem
    exact sub_eq_zero.mp (hz hmem)
  have htrans : ∀ᵐ z ∂(volume : Measure ℂ),∀ m : Eisenstein,
      z+3*(m:ℂ)∈cubicThetaHorizontalCell → f z=g z := by
    apply ae_all_iff.mpr
    intro m
    have ht := (measurePreserving_add_right volume (3*(m:ℂ))).quasiMeasurePreserving.ae hcell'
    filter_upwards [ht] with z hz hmem
    simpa only [hfp m z,hgp m z] using hz hmem
  have hall : f=ᵐ[(volume : Measure ℂ)] g := by
    filter_upwards [htrans] with z hz
    obtain ⟨m,hm,_⟩ := cubicThetaHorizontalCell_unique z
    exact hz (Multiplicative.toAdd m) hm
  exact Measure.eq_of_ae_eq hall hf hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactBorelRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded compact restriction of the actual global L2 lift. This
permits cusp Fourier windows after arbitrary integral coordinate changes. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaCompactBorelRestriction_coe {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaGlobalL2) :
    cubicThetaCompactBorelRestriction hK F =ᵐ[cubicThetaPointMeasure.restrict K]
      cubicThetaBorelLift (F : CubicThetaQuotient → ℂ) :=
  (cubicThetaBorelLift_compact_memLp hK
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp

lemma cubicThetaCompactBorelRestriction_section {K : Set CubicThetaPoint} (hK : IsCompact K)
    (F : CubicThetaSection) (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    cubicThetaCompactBorelRestriction hK (hF.toLp _)=ᵐ[cubicThetaPointMeasure.restrict K] F.val := by
  filter_upwards [cubicThetaCompactBorelRestriction_coe hK (hF.toLp _),
    cubicThetaCompact_pull_ae hK hF.coeFn_toLp] with p hp hq
  rw [hp]
  change cubicThetaBorelPhase p*(hF.toLp _) (cubicThetaQuotientMap p)=_
  rw [hq]
  exact cubicThetaBorelLift_section F p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactIntegralRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sampling after a literal integral Mobius transformation.
The map acts on actual global L2 vectors and retains the cubic Borel phase. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompactIntegralRestriction_coe (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaGlobalL2) :
    cubicThetaCompactIntegralRestriction δ hK F=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => cubicThetaBorelLift F (δ • p)) := by
  have hp := cubicThetaCompactIntegral_measure δ hK
  have hB := cubicThetaCompactBorelRestriction_coe (hK.image (continuous_const_smul δ)) F
  have ht := hp.quasiMeasurePreserving.ae hB
  have hc := Lp.coeFn_compMeasurePreserving
    (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)) F) hp
  exact hc.trans ht

lemma cubicThetaCompactIntegralRestriction_section (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    cubicThetaCompactIntegralRestriction δ hK (hF.toLp _)=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => F.val (δ • p)) := by
  have hp := cubicThetaCompactIntegral_measure δ hK
  have hB := cubicThetaCompactBorelRestriction_section (hK.image (continuous_const_smul δ)) F hF
  have ht := hp.quasiMeasurePreserving.ae hB
  have hc := Lp.coeFn_compMeasurePreserving
    (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)) (hF.toLp _)) hp
  exact hc.trans ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows at the translated inverted cusps used by the primary
coefficient projector. The phase is kept as the actual cubic symbol; its
ramified evaluation is a subsequent arithmetic step. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaShiftedInversion_complex (b : Eisenstein) :
    cubicThetaFullComplex (cubicThetaShiftedInversion b) =
      cubicThetaTranslationMatrix (b:ℂ)*cubicThetaInversionMatrix 1 one_ne_zero := by
  have he : cubicThetaShiftedInversion b = cubicThetaFullTranslation b*cubicThetaFullInversion := by
    apply Subtype.ext
    change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]
  rw [he,map_mul,cubicThetaFullTranslation_complex,cubicThetaFullInversion_complex]

lemma cubicThetaMobius_shiftedInversion (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) :
    cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p =
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) := by
  rw [cubicThetaShiftedInversion_complex,←cubicThetaMobius_comp _ _ hp,
    cubicThetaMobius_translation,cubicThetaMobius_inversion one_ne_zero hp]

lemma cubicThetaBottomRow_height_shiftedInverted (r : CubicThetaBottomRow)
    (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) =
      (cubicThetaShiftedInvertedRowEquiv b r).height p := by
  rw [cubicThetaBottomRow_height_full r _ hp]
  simp only [cubicThetaShiftedInversion,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_zero,mul_one,mul_neg_one,add_zero]
  change p.2/(Complex.normSq ((((r.c*b+r.d:Eisenstein):ℂ)*p.1+(-r.c:Eisenstein)))+
    norm (r.c*b+r.d)*p.2^2)=_
  have he : r.c*b+r.d=r.d+b*r.c := by ring
  rw [he]
  rfl

theorem cubicThetaEisenstein_shiftedInverted {p : ℂ×ℝ} (hp : 0<p.2)
    (b : Eisenstein) (s : ℂ) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s =
      ∑' r : CubicThetaInvertedRow, cubicThetaShiftedInvertedTerm b r p s := by
  rw [←cubicThetaMobius_shiftedInversion b hp]
  unfold cubicThetaEisenstein
  have he (r : CubicThetaBottomRow) :
      cubicThetaEisensteinTerm r
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s =
      cubicThetaShiftedInvertedTerm b (cubicThetaShiftedInvertedRowEquiv b r) p s := by
    rw [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,star_star,
      cubicThetaBottomRow_height_shiftedInverted r b hp]
    dsimp only [cubicThetaShiftedInvertedTerm,cubicThetaShiftedInvertedRowEquiv,Equiv.coe_fn_mk]
    have hx : r.d+b*r.c+b*(-r.c)=r.d := by ring
    rw [hx,cubicSymbol_neg r.d_primary]
  simp_rw [he]
  exact (cubicThetaShiftedInvertedRowEquiv b).tsum_eq
    (fun r => cubicThetaShiftedInvertedTerm b r p s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCuspPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodicity of the actual translated-cusp row phase. Conjugating a
translation by the cusp matrix gives a principal level-nine matrix with
trivial Kubota value, proved from the supplementary laws. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaShiftedRowTranslate_action (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    ((cubicThetaShiftedInvertedRowEquiv b).symm r).rightMul (cubicThetaCuspTranslation b m) =
      (cubicThetaShiftedInvertedRowEquiv b).symm (cubicThetaShiftedRowTranslate r m) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change (-r.d)*(1-9*b*m)+(r.c+b*r.d)*(-9*m)= -(r.d+9*m*r.c)
    ring
  · rw [CubicThetaBottomRow.rightMul_d]
    change (-r.d)*(9*b^2*m)+(r.c+b*r.d)*(1+9*b*m)=r.c+b*(r.d+9*m*r.c)
    ring

lemma cubicThetaShiftedRowPhase_eq (b : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b r=
      star (((cubicThetaShiftedInvertedRowEquiv b).symm r).phase) := by
  change cubicSymbol (r.c+b*r.d) r.d=star (star (cubicSymbol (r.c+b*r.d) (-r.d)))
  rw [star_star,cubicSymbol_neg (cubicTheta_primary_add_three_mul r.c_primary r.d_three b)]

lemma cubicThetaShiftedRowPhase_periodic (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b (cubicThetaShiftedRowTranslate r m)=
      cubicThetaShiftedRowPhase b r := by
  have he := ((cubicThetaShiftedInvertedRowEquiv b).symm r).phase_rightMul
    (cubicThetaCuspTranslation b m)
  rw [cubicThetaShiftedRowTranslate_action,cubicThetaCuspTranslation_value,mul_one] at he
  rw [cubicThetaShiftedRowPhase_eq,cubicThetaShiftedRowPhase_eq,he]

lemma cubicThetaShiftedRowPhase_norm (b : Eisenstein) (r : CubicThetaInvertedRow) :
    ‖cubicThetaShiftedRowPhase b r‖=1 := by
  rw [cubicThetaShiftedRowPhase_eq,norm_star,CubicThetaBottomRow.phase_norm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero-extended periodic weights of the translated inverted rows.
The finite residue modulus is `3*c` in the variable `d=3*u`. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaShiftedRowWeight_norm {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) : ‖cubicThetaShiftedRowWeight b c u‖ ≤ 1 :=
  norm_cubicSymbol_le_one (cubicTheta_primary_add_three_mul hc ⟨u,rfl⟩ b) _

lemma cubicThetaShiftedRowWeight_periodic {c : Eisenstein} (hc : primary c)
    (b u m : Eisenstein) :
    cubicThetaShiftedRowWeight b c (u+(3*c)*m)=cubicThetaShiftedRowWeight b c u := by
  have hd : 3*(u+(3*c)*m)=3*u+9*m*c := by ring
  by_cases hcop : IsCoprime c (3*u)
  · let r : CubicThetaInvertedRow := ⟨c,3*u,hc,⟨u,rfl⟩,hcop⟩
    have he := cubicThetaShiftedRowPhase_periodic b m r
    simpa only [cubicThetaShiftedRowPhase,cubicThetaShiftedRowTranslate,r,
      cubicThetaShiftedRowWeight,hd] using he
  · have hcop' : ¬IsCoprime c (3*(u+(3*c)*m)) := by
      rw [hd,cubicTheta_coprime_add_right]
      exact hcop
    have hz (v : Eisenstein) (hv : ¬IsCoprime c (3*v)) : cubicThetaShiftedRowWeight b c v=0 := by
      apply cubicSymbol_eq_zero_of_not_isCoprime
        (cubicTheta_primary_add_three_mul hc ⟨v,rfl⟩ b)
      rwa [cubicTheta_coprime_add_left]
    rw [hz _ hcop',hz _ hcop]

lemma cubicThetaShiftedRowWeight_congr {c u v : Eisenstein} (hc : primary c)
    (b : Eisenstein) (h : (3*c)∣u-v) :
    cubicThetaShiftedRowWeight b c u=cubicThetaShiftedRowWeight b c v := by
  obtain ⟨m,hm⟩ := h
  have he : u=v+(3*c)*m := by linear_combination hm
  rw [he,cubicThetaShiftedRowWeight_periodic hc]

lemma cubicThetaShiftedResidueWeight_mk {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    cubicThetaShiftedResidueWeight b c (Ideal.Quotient.mk (modulus (3*c)) u)=
      cubicThetaShiftedRowWeight b c u := by
  apply cubicThetaShiftedRowWeight_congr hc b
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus (3*c))
    (residueRepresentative (3*c) (Ideal.Quotient.mk (modulus (3*c)) u)-u)=0
  rw [map_sub,residueRepresentative_spec,sub_self]

lemma cubicThetaShiftedGaussCoefficient_norm {c : Eisenstein} (hc : primary c)
    (b h : Eisenstein) :
    ‖cubicThetaShiftedGaussCoefficient b c h‖ ≤ (Nat.card (Residues (3*c)):ℝ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) (primary_ne_zero hc))
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  unfold cubicThetaShiftedGaussCoefficient
  rw [tsum_fintype,Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues (3*c), ‖cubicThetaShiftedResidueWeight b c x*
        (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
          ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues (3*c), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul,Circle.norm_coe,mul_one]
      exact cubicThetaShiftedRowWeight_norm hc b _
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal primary-row unfolding at every translated inverted cusp.
Absolute convergence follows from equality of the actual row norms. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaShiftedGridTerm_admissible (b : Eisenstein)
    (cd : {cd // cubicThetaInvertedAdmissible cd}) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaShiftedGridTerm b cd.val p s=
      cubicThetaShiftedInvertedTerm b (cubicThetaInvertedPairEquiv.symm cd) p s := by
  simp only [cubicThetaShiftedGridTerm,cd.property,ite_true, if_true,cubicThetaShiftedInvertedTerm,
    cubicThetaInvertedPairEquiv,CubicThetaInvertedRow.height]
  rfl

lemma cubicThetaShiftedInvertedTerm_norm (b : Eisenstein) (r : CubicThetaInvertedRow)
    (p : ℂ×ℝ) (s : ℂ) :
    ‖cubicThetaShiftedInvertedTerm b r p s‖=‖cubicThetaInvertedTerm r p s‖ := by
  unfold cubicThetaShiftedInvertedTerm cubicThetaInvertedTerm
  rw [norm_mul,norm_mul,norm_cubicSymbol_of_isCoprime r.c_primary r.coprime]
  have hn := cubicThetaShiftedRowPhase_norm b r
  change ‖cubicSymbol (r.c+b*r.d) r.d‖=1 at hn
  rw [hn]

lemma cubicThetaShiftedInvertedTerm_summable {p : ℂ×ℝ} (hp : 0<p.2)
    (b : Eisenstein) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r : CubicThetaInvertedRow => cubicThetaShiftedInvertedTerm b r p s) := by
  apply Summable.of_norm
  simpa only [cubicThetaShiftedInvertedTerm_norm] using (cubicThetaInvertedTerm_summable hp hs).norm

lemma cubicThetaShiftedGrid_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaShiftedGridTerm b cd p s) := by
  have hsub := (cubicThetaShiftedInvertedTerm_summable hp b hs).comp_injective
    cubicThetaInvertedPairEquiv.symm.injective
  have hg : Summable (fun cd : {cd // cubicThetaInvertedAdmissible cd} =>
      cubicThetaShiftedGridTerm b cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaShiftedGridTerm_admissible b cd p s).symm
  apply (Subtype.val_injective.summable_iff
    (f:=fun cd => cubicThetaShiftedGridTerm b cd p s) ?_).mp hg
  intro cd hcd
  by_cases hc : cubicThetaInvertedAdmissible cd
  · exact False.elim (hcd ⟨⟨cd,hc⟩,rfl⟩)
  · simp [cubicThetaShiftedGridTerm,hc]

theorem cubicThetaEisenstein_shifted_grid (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' cd : Eisenstein × Eisenstein, cubicThetaShiftedGridTerm b cd p s := by
  rw [cubicThetaEisenstein_shiftedInverted hp b]
  have hsup : Function.support (fun cd => cubicThetaShiftedGridTerm b cd p s) ⊆
      {cd | cubicThetaInvertedAdmissible cd} := by
    intro cd hcd
    by_contra hc
    change ¬cubicThetaInvertedAdmissible cd at hc
    exact hcd (by simp [cubicThetaShiftedGridTerm,hc])
  calc
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd},
        cubicThetaShiftedInvertedTerm b (cubicThetaInvertedPairEquiv.symm cd) p s :=
      (cubicThetaInvertedPairEquiv.symm.tsum_eq _).symm
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd}, cubicThetaShiftedGridTerm b cd.val p s :=
      tsum_congr (fun cd => (cubicThetaShiftedGridTerm_admissible b cd p s).symm)
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaShiftedGridTerm_triple (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    (a : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaShiftedGridTerm b (c,3*a) p s=
      cubicThetaShiftedRowWeight b c a*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+3*(a:ℂ))+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hcop : IsCoprime c (3*a)
  · have h3 : ((3:Eisenstein):ℂ)=(3:ℂ) := rfl
    simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,cubicThetaShiftedRowWeight,hc,hcop,h3]
  · simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,hcop,
      cubicThetaShiftedRowWeight,
      cubicSymbol_eq_zero_of_not_isCoprime
        (cubicTheta_primary_add_three_mul hc ⟨a,rfl⟩ b)
        ((cubicTheta_coprime_add_left c (3*a) b).not.mpr hcop)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactShiftedFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded observations of the actual translated-cusp Eisenstein family.
Their residues are the already constructed arithmetic theta model, sampled
at the same Mobius transform. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaCompactShiftedFamily_meromorphic (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaCompactShiftedFamily b hK) s := by
  apply cubicThetaMeromorphic_clm (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK)
  exact (cubicThetaForcedResolvent_meromorphic hs).const_smul cubicThetaResidueScale

lemma cubicThetaCompactShiftedFamily_residue (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) :
    Tendsto (fun s : ℂ => (s-4/3) • cubicThetaCompactShiftedFamily b hK s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue))) := by
  let L := cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
  have ht := (L.continuous.tendsto _).comp
    ((continuous_const_smul cubicThetaResidueScale).tendsto _ |>.comp
      (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)))
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at ht
  change Tendsto (fun s : ℂ => L (cubicThetaResidueScale • ((s-4/3) • cubicThetaForcedResolvent s)))
    (𝓝[≠] (4/3:ℂ))
    (𝓝 (L (cubicThetaResidueScale • cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) at ht
  rw [cubicThetaNormalizedArithmeticResidue,map_smul]
  apply ht.congr'
  filter_upwards with s
  change L (cubicThetaResidueScale • ((s-4/3) • cubicThetaForcedResolvent s))=
    (s-4/3) • L (cubicThetaResidueScale • cubicThetaForcedResolvent s)
  rw [smul_comm cubicThetaResidueScale (s-4/3),map_smul]

lemma cubicThetaCompactShiftedResidue_model (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) :
    cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure.restrict K]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
          (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
  have hmodel := (measurePreserving_smul (cubicThetaShiftedInversion b)
    cubicThetaPointMeasure).quasiMeasurePreserving.ae cubicThetaArithmeticModel_global_ae
  filter_upwards [cubicThetaCompactIntegralRestriction_coe (cubicThetaShiftedInversion b) hK
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue),
    ae_restrict_of_ae hmodel] with p hp hmp
  exact hp.trans hmp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactShiftedObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded scalar observations of the translated family and its actual residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaCompactShiftedObservation_meromorphic (b : Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K)
    (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaCompactShiftedObservation b hK T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaCompactShiftedFamily_meromorphic b hK hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-step translation character of a shifted cusp. It supplies
the ramified finite Fourier factor before the unramified Gauss sum. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaShiftedRowStep_action (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    ((cubicThetaShiftedInvertedRowEquiv b).symm r).rightMul (cubicThetaCuspStep b m) =
      (cubicThetaShiftedInvertedRowEquiv b).symm (cubicThetaShiftedRowStep r m) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change (-r.d)*(1-3*b*m)+(r.c+b*r.d)*(-3*m)= -(r.d+3*m*r.c)
    ring
  · rw [CubicThetaBottomRow.rightMul_d]
    change (-r.d)*(3*b^2*m)+(r.c+b*r.d)*(1+3*b*m)=r.c+b*(r.d+3*m*r.c)
    ring

lemma cubicThetaShiftedRowPhase_step (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b (cubicThetaShiftedRowStep r m)=
      star (cubicThetaCuspStepValue b m)*cubicThetaShiftedRowPhase b r := by
  have he := ((cubicThetaShiftedInvertedRowEquiv b).symm r).phase_rightMul (cubicThetaCuspStep b m)
  rw [cubicThetaShiftedRowStep_action] at he
  rw [cubicThetaShiftedRowPhase_eq,cubicThetaShiftedRowPhase_eq,he,star_mul]
  rfl

lemma cubicThetaShiftedRowWeight_step {c : Eisenstein} (hc : primary c)
    (b u m : Eisenstein) :
    cubicThetaShiftedRowWeight b c (u+c*m)=
      star (cubicThetaCuspStepValue b m)*cubicThetaShiftedRowWeight b c u := by
  have hd : 3*(u+c*m)=3*u+3*m*c := by ring
  by_cases hcop : IsCoprime c (3*u)
  · let r : CubicThetaInvertedRow := ⟨c,3*u,hc,⟨u,rfl⟩,hcop⟩
    have he := cubicThetaShiftedRowPhase_step b m r
    simpa only [cubicThetaShiftedRowPhase,cubicThetaShiftedRowStep,r,
      cubicThetaShiftedRowWeight,hd] using he
  · have hz (v : Eisenstein) (hv : ¬IsCoprime c (3*v)) : cubicThetaShiftedRowWeight b c v=0 := by
      apply cubicSymbol_eq_zero_of_not_isCoprime (cubicTheta_primary_add_three_mul hc ⟨v,rfl⟩ b)
      rwa [cubicTheta_coprime_add_left]
    have hcop' : ¬IsCoprime c (3*(u+c*m)) := by
      rw [hd,cubicTheta_coprime_add_right]
      exact hcop
    rw [hz _ hcop',hz _ hcop,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit additive character at an integral translated cusp. Its
frequency is determined by the omega coordinate of the translation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCuspCharacter_one (b : Eisenstein) :
    cubicThetaCuspCharacter b 1=(cubicThetaRamifiedCharacter (-b))^2 := by
  have hp : primary (1-3*b) := ⟨-b,by ring⟩
  change (if (-3*(1:Eisenstein))=0 then 1 else cubicSymbol (1-3*b*1) (-3*1))=_
  norm_num only [mul_one,neg_ne_zero,OfNat.ofNat_ne_zero,ite_false]
  rw [cubicSymbol_neg hp,cubicThetaSymbol_three hp,show 1-3*b=1+3*(-b) by ring]
  rfl

lemma cubicThetaCuspCharacter_omega (b : Eisenstein) :
    cubicThetaCuspCharacter b omegaE=
      (cubicThetaRamifiedCharacter (-b*omegaE))^2*cubicThetaUnitCharacter (-b*omegaE) := by
  have hp : primary (1-3*b*omegaE) := ⟨-b*omegaE,by ring⟩
  have hn : (-3*omegaE:Eisenstein)≠0 :=
    mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (omegaE_primitive.ne_zero (by norm_num))
  change (if (-3*omegaE:Eisenstein)=0 then 1 else
    cubicSymbol (1-3*b*omegaE) (-3*omegaE))=_
  rw [ite_eq_right hn,show (-3*omegaE:Eisenstein)= -(3*omegaE) by ring,
    cubicSymbol_neg hp,cubicSymbol_mul_upper hp,cubicThetaSymbol_three hp,
    show 1-3*b*omegaE=1+3*(-b*omegaE) by ring]
  rfl

lemma cubicTheta_omega_zpow_add_three (a b : ℤ) : omega^(a+3*b)=omega^a := by
  rw [zpow_add₀ (omega_primitive.ne_zero (by norm_num)),zpow_mul]
  have h3 : omega^(3:ℤ)=1 := by norm_num [omega_cube]
  rw [h3,one_zpow,mul_one]

lemma cubicThetaCuspCharacter_coordinates (a b : ℤ) :
    cubicThetaCuspCharacter ((a:Eisenstein)+b*omegaE)=
      cubicThetaUnitCharacter.mulShift (b:Eisenstein) := by
  apply cubicThetaAddChar_eq_of_generators
  · rw [cubicThetaCuspCharacter_one]
    have hn : -((a:Eisenstein)+b*omegaE)=(((-a:ℤ):Eisenstein)+((-b:ℤ):Eisenstein)*omegaE) := by push_cast; ring
    rw [hn,cubicThetaRamifiedCharacter_coordinates]
    change (omega^(2*(-b)))^2=cubicThetaUnitCharacter ((b:Eisenstein)*1)
    have hU : cubicThetaUnitCharacter (b:Eisenstein)=omega^(2*b) := by
      simpa only [Int.cast_zero,zero_mul,add_zero,add_zero] using
        cubicThetaUnitCharacter_coordinates b 0
    rw [mul_one,hU]
    rw [←zpow_natCast (omega^(2*(-b))) 2,←zpow_mul]
    convert cubicTheta_omega_zpow_add_three (2*b) (-2*b) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · rw [cubicThetaCuspCharacter_omega]
    have hn : -((a:Eisenstein)+b*omegaE)*omegaE=
        (b:Eisenstein)+((b-a:ℤ):Eisenstein)*omegaE := by
      push_cast
      linear_combination -(b:Eisenstein)*omegaE_quadratic
    rw [hn,cubicThetaRamifiedCharacter_coordinates,cubicThetaUnitCharacter_coordinates]
    change (omega^(2*(b-a)))^2*omega^(2*(b+(b-a)))=
      cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)
    have hU : cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)=omega^(2*b) := by
      simpa only [Int.cast_zero,zero_add,zero_add] using
        cubicThetaUnitCharacter_coordinates 0 b
    rw [hU]
    rw [←zpow_natCast (omega^(2*(b-a))) 2,←zpow_mul,
      ←zpow_add₀ (omega_primitive.ne_zero (by norm_num))]
    convert cubicTheta_omega_zpow_add_three (2*b) (2*b-2*a) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

theorem cubicThetaCuspStepValue_fourier (a b : ℤ) (m : Eisenstein) :
    cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) m=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*((b:Eisenstein)*m))) := by
  change cubicThetaCuspCharacter ((a:Eisenstein)+b*omegaE) m=_
  rw [cubicThetaCuspCharacter_coordinates]
  exact cubicThetaUnitCharacter_fourier _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFourierSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted-cusp finite Fourier coefficient can be nonzero
only at frequencies matching its ramified translation character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaShiftedGaussCoefficient_fourier {c : Eisenstein} (hc : c≠0)
    (b h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient b c h=
      ∑' x : Residues (3*c), cubicThetaShiftedResidueWeight b c x*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
          (Ideal.Quotient.mk (modulus (3*c)) h*x) := by
  unfold cubicThetaShiftedGaussCoefficient
  apply tsum_congr
  intro x
  rw [residueFourierChar_mk_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWeightFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the ramified cusp character from the ordinary cubic row
weight, using the proved step law and elementary reciprocity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaShiftedRowWeight_of_three_dvd {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) (hu : (3:Eisenstein) ∣ u) :
    cubicThetaShiftedRowWeight b c u=cubicSymbol c (3*u) := by
  unfold cubicThetaShiftedRowWeight
  apply cubicSymbol_periodic_of_nine_and_numerator
    (cubicTheta_primary_add_three_mul hc ⟨u,rfl⟩ b) hc
  · obtain ⟨v,rfl⟩ := hu
    exact ⟨b*v,by ring⟩
  · exact ⟨b,by ring⟩

lemma cubicThetaShiftedRowWeight_factor {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    cubicThetaShiftedRowWeight b c u=
      star (cubicThetaCuspStepValue b u)*cubicSymbol c (3*u) := by
  let v := (1-c)*u
  have hv : (3:Eisenstein) ∣ v := by
    obtain ⟨k,hk⟩ := hc
    exact ⟨-k*u,by dsimp only [v]; linear_combination -u*hk⟩
  have hs := cubicThetaShiftedRowWeight_step hc b v u
  have he : v+c*u=u := by dsimp only [v]; ring
  rw [he,cubicThetaShiftedRowWeight_of_three_dvd hc b v hv] at hs
  have hr : cubicSymbol c (3*v)=cubicSymbol c (3*u) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    exact ⟨-3*u,by dsimp only [v]; ring⟩
  rwa [hr] at hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedGaussReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reduction of the translated-cusp Fourier coefficients to
ordinary primary cubic Gauss coefficients, with the ramified shift retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCuspStepValue_star_mul (b m : Eisenstein) :
    star (cubicThetaCuspStepValue b m)*cubicThetaCuspStepValue b m=1 := by
  rw [mul_comm,Complex.star_def,Complex.mul_conj']
  change (‖cubicThetaKubotaValue (cubicThetaCuspStep b m)‖:ℂ)^2=1
  rw [cubicThetaKubotaValue_norm]
  norm_num

lemma cubicThetaShiftedGauss_phase {c : Eisenstein} (hc : c≠0)
    (a b : ℤ) (x : Residues (3*c)) :
    residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
        (Ideal.Quotient.mk (modulus (3*c)) (c*lambdaE*(b:Eisenstein))*x)=
      cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x) := by
  rw [cubicThetaCuspStepValue_fourier]
  have hx := residueRepresentative_spec (3*c) x
  conv_lhs => rw [←hx,←map_mul]
  rw [show c*lambdaE*(b:Eisenstein)*residueRepresentative (3*c) x=
    c*(lambdaE*(b:Eisenstein))*residueRepresentative (3*c) x by ring,
    residueFourierChar_mul_factor (by norm_num) hc]
  congr 2
  ring

lemma cubicThetaInvertedWeight_reduction {c : Eisenstein} (hc : primary c)
    (x : Residues (3*c)) :
    cubicSymbol c (3*residueRepresentative c
      (residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x))=
      cubicSymbol c (3*residueRepresentative (3*c) x) := by
  have he : residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x=
      Ideal.Quotient.mk (modulus c) (residueRepresentative (3*c) x) := by
    rw [←residueReduction_mk (show c ∣ 3*c from ⟨3,by ring⟩),residueRepresentative_spec]
  rw [he,cubicThetaInvertedResidueWeight_mk hc]

theorem cubicThetaShiftedGaussCoefficient_untwist {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h=
      ∑' x : Residues (3*c),
        cubicSymbol c (3*residueRepresentative c
          (residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x))*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) (primary_ne_zero hc))
          (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x) := by
  rw [cubicThetaShiftedGaussCoefficient_fourier (primary_ne_zero hc)]
  apply tsum_congr
  intro x
  let ψ := residueFourierChar (3*c) (mul_ne_zero (by norm_num) (primary_ne_zero hc))
  have he : ψ (Ideal.Quotient.mk (modulus (3*c)) h*x)=
      ψ (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x)*
      ψ (Ideal.Quotient.mk (modulus (3*c)) (c*lambdaE*(b:Eisenstein))*x) := by
    rw [←ψ.map_add_eq_mul,←add_mul,←map_add,sub_add_cancel]
  have hw : cubicThetaShiftedResidueWeight ((a:Eisenstein)+b*omegaE) c x=
      star (cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x))*
        cubicSymbol c (3*residueRepresentative (3*c) x) :=
    cubicThetaShiftedRowWeight_factor hc _ _
  rw [hw,he,cubicThetaShiftedGauss_phase (primary_ne_zero hc) a b x,
    cubicThetaInvertedWeight_reduction hc x]
  have hχ := cubicThetaCuspStepValue_star_mul ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x)
  linear_combination cubicSymbol c (3*residueRepresentative (3*c) x)*
    ψ (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x)*hχ

theorem cubicThetaShiftedGaussCoefficient_reduce {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c
      (3*h+c*lambdaE*(b:Eisenstein))=9*cubicThetaInvertedGaussCoefficient c h := by
  have hc0 := primary_ne_zero hc
  have h3 : (3:Eisenstein)≠0 := by norm_num
  rw [cubicThetaShiftedGaussCoefficient_untwist hc,add_sub_cancel_right]
  rw [residueFourier_inflation_of_eq (mul_ne_zero h3 hc0) hc0 h3
    (show 3*c=c*3 by ring) (show c ∣ 3*c from ⟨3,by ring⟩)
    (fun y => cubicSymbol c (3*residueRepresentative c y)) h]
  have hN : (norm (3:Eisenstein):ℂ)=9 := by
    change (Complex.normSq (3:ℂ):ℂ)=9
    norm_num
  rw [hN]
  congr 1
  unfold cubicThetaInvertedGaussCoefficient
  apply tsum_congr
  intro y
  rw [residueFourierChar_mk_mul]

theorem cubicThetaShiftedGaussCoefficient_congruence {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein)
    (hF : cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h≠0) :
    (3:Eisenstein) ∣ h-c*lambdaE*(b:Eisenstein) := by
  have hc0 := primary_ne_zero hc
  have hq : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  let : Finite (Residues (3*c)) := finite_residues hq
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  rw [cubicThetaShiftedGaussCoefficient_untwist hc,tsum_fintype] at hF
  have he := residueFourier_inflation_support hq (show c ∣ 3*c from ⟨3,by ring⟩)
    (fun y => cubicSymbol c (3*residueRepresentative c y)) (h-c*lambdaE*(b:Eisenstein)) hF
  rwa [mul_comm (3:Eisenstein) c,mul_dvd_mul_iff_left hc0] at he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedGaussExplicit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit translated-cusp Gauss coefficients. The only new support
condition is the ramified congruence; the unramified factor is the same
primary Fourier coefficient already identified from the actual residue. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaSymbolFourier_congr {c : Eisenstein} (hc : c≠0)
    {h k : Eisenstein} (he : c ∣ h-k) :
    cubicThetaSymbolFourier c hc h=cubicThetaSymbolFourier c hc k := by
  unfold cubicThetaSymbolFourier
  have hm := residue_eq_of_dvd_sub he
  apply tsum_congr
  intro x
  rw [hm]

lemma cubicThetaInvertedGaussCoefficient_shift {c : Eisenstein} (hc : primary c)
    (k h : Eisenstein) (he : c ∣ 3*k-h) :
    cubicThetaInvertedGaussCoefficient c k=
      cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  have hcub := cubicSymbol_cube_of_isCoprime hc lambdaE (primary_coprime_lambda hc)
  have hs : star (cubicSymbol c 3)=cubicSymbol c lambdaE := by
    rw [cubicThetaSymbol_three hc,star_pow,←cubicSymbol_sq_eq_star hc]
    calc
      (cubicSymbol c lambdaE^2)^2=(cubicSymbol c lambdaE)^3*cubicSymbol c lambdaE := by ring
      _ = _ := by rw [hcub,one_mul]
  have hG : cubicThetaSymbolFourier c (primary_ne_zero hc) h=
      cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) k := by
    rw [←cubicThetaSymbolFourier_congr (primary_ne_zero hc) he,
      mul_comm (3:Eisenstein) k,cubicThetaSymbolFourier_mul hc (primary_coprime_three hc),hs]
  rw [cubicThetaInvertedGaussCoefficient_factor hc,cubicThetaSymbol_three hc,hG]
  ring

lemma cubicThetaShiftedGauss_congruence_iff {c : Eisenstein} (hc : primary c)
    (b : ℤ) (h : Eisenstein) :
    (3:Eisenstein) ∣ h-c*lambdaE*(b:Eisenstein) ↔
      (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) := by
  have hd : (3:Eisenstein) ∣ (c-1)*lambdaE*(b:Eisenstein) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
  constructor
  · intro hh
    convert dvd_add hh hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro hh
    convert dvd_sub hh hd using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem cubicThetaShiftedGaussCoefficient_explicit {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) h else 0 := by
  classical
  by_cases ht : (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein)
  · rw [ite_eq_left ht]
    obtain ⟨k,hk⟩ := (cubicThetaShiftedGauss_congruence_iff hc b h).mpr ht
    have he : h=3*k+c*lambdaE*(b:Eisenstein) := by linear_combination hk
    rw [he,cubicThetaShiftedGaussCoefficient_reduce hc]
    rw [cubicThetaInvertedGaussCoefficient_shift hc k (3*k+c*lambdaE*(b:Eisenstein))
      ⟨-lambdaE*(b:Eisenstein),by ring⟩]
    ring
  · rw [ite_eq_right ht]
    by_contra hn
    exact ht ((cubicThetaShiftedGauss_congruence_iff hc b h).mp
      (cubicThetaShiftedGaussCoefficient_congruence hc a b h hn))

theorem cubicThetaShiftedFrequencyDirichlet_eq (a b : ℤ) (h : Eisenstein) (s : ℂ) :
    cubicThetaShiftedFrequencyDirichlet ((a:Eisenstein)+b*omegaE) h s=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicThetaPrimaryFourierSeries 1 2 s h else 0 := by
  classical
  unfold cubicThetaShiftedFrequencyDirichlet
  have he (c : CubicThetaPrimaryPart) :
      cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c.val h=
        if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
          9*cubicSymbol c.val lambdaE*cubicThetaSymbolFourier c.val (primary_ne_zero c.property) h else 0 :=
    cubicThetaShiftedGaussCoefficient_explicit c.property a b h
  simp_rw [he]
  split_ifs with ht
  · unfold cubicThetaPrimaryFourierSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro c
    unfold cubicThetaPrimaryFourierTerm
    have hu : cubicSymbol c.val 1=1 := by
      rw [cubic_reciprocity c.property primary_one,cubicSymbol_one_lower]
    have hcub := cubicSymbol_cube_of_isCoprime c.property lambdaE (primary_coprime_lambda c.property)
    rw [Units.val_one,hu,one_mul]
    have hp : ((cubicSymbol c.val lambdaE)^2)^2=cubicSymbol c.val lambdaE := by
      calc
        _ = (cubicSymbol c.val lambdaE)^3*cubicSymbol c.val lambdaE := by ring
        _ = _ := by rw [hcub,one_mul]
    rw [hp]
    ring
  · simp only [zero_mul,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedHeatSummability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency and summable heat majorant at the translated cusps. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaShiftedRowHeatScale_eq (h : Eisenstein) :
    cubicThetaShiftedRowHeatScale h=(4*Real.pi^2/243)*norm h := by
  unfold cubicThetaShiftedRowHeatScale cubicThetaShiftedRowFrequency
  rw [Complex.normSq_div,map_mul,traceLambda_normSq]
  norm_num
  change 4*Real.pi^2*(norm h/243)=_
  ring

lemma cubicThetaShiftedRowHeatScale_pos {h : Eisenstein} (hh : h≠0) :
    0 < cubicThetaShiftedRowHeatScale h := by
  rw [cubicThetaShiftedRowHeatScale_eq]
  exact mul_pos (by positivity) (norm_pos_of_ne_zero hh)

@[simp] lemma cubicThetaShiftedRowHeatScale_zero : cubicThetaShiftedRowHeatScale 0=0 := by
  simp [cubicThetaShiftedRowHeatScale_eq,norm]

theorem cubicThetaShiftedDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t‖) := by
  let b : ℝ := 4*Real.pi^2/243
  have hb : 0 < b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))
  have hJ : 0 ≤ J := by
    apply mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
    exact Real.rpow_nonneg (sq_nonneg v) _
  let K : ℝ := (2/b^2)*J
  have hK : 0 ≤ K := mul_nonneg (by positivity) hJ
  let m0 : ℝ := ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s 0 t‖
  have hm0 : 0 ≤ m0 := integral_nonneg (fun _ => _root_.norm_nonneg _)
  have ht := (hasSum_ite_eq (0:Eisenstein) m0).summable.add
    ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left K)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h = 0
    · subst h
      simp only [cubicThetaShiftedRowHeatScale_zero, ite_true, if_true]
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
    · simp only [hh, ite_false, if_false, zero_add]
      apply (cubicThetaDualHeat_norm_mass_bound hv hs (cubicThetaShiftedRowHeatScale_pos hh)).trans_eq
      rw [cubicThetaShiftedRowHeatScale_eq]
      change (2/(b*norm h)^2)*J = K*(norm h)^(-(2:ℝ))
      rw [Real.rpow_neg (norm_nonneg h), Real.rpow_two]
      dsimp [K]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCuspGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson summation at each translated inverted cusp. The true period
is 3c in the row variable and the dual frequency is h/(9 lambda). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaShiftedCuspGaussianRow_poisson {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaShiftedCuspGaussianRow b c z t=
      (2/(81*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedGaussCoefficient b c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ)) := by
  have hc0 := primary_ne_zero hc
  have hcC : (c:ℂ)≠0 := fun h => hc0 (Subtype.ext h)
  have hc3 : (c:ℂ)/3≠0 := div_ne_zero hcC (by norm_num)
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  have hp := poisson_eisenstein_periodic (3*c) h3c
    (cubicThetaShiftedResidueWeight b c)
    (cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht)
  have hleft : (∑' a : Eisenstein,
      cubicThetaShiftedResidueWeight b c (Ideal.Quotient.mk (modulus (3*c)) a)*
        cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht (a:ℂ))=
      cubicThetaShiftedCuspGaussianRow b c z t := by
    apply tsum_congr
    intro a
    rw [cubicThetaShiftedResidueWeight_mk hc,cubicThetaShiftedGaussian_apply]
    congr 4
    field_simp
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))*((c:ℂ)/3)=
      (h:ℂ)/(9*traceLambda) := by
    push_cast
    simp only [show ((3:Eisenstein):ℂ)=3 from rfl]
    field_simp
    ring
  simp_rw [cubicThetaShiftedGaussian_fourier,hfreq] at hp
  change cubicThetaShiftedCuspGaussianRow b c z t=
    (2/(Real.sqrt 3*norm (3*c)):ℝ) •
      ∑' h : Eisenstein, cubicThetaShiftedGaussCoefficient b c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm (3*c)):ℝ):ℂ)*_=_
  have hf : (∑' h : Eisenstein, cubicThetaShiftedGaussCoefficient b c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ))))=
      (Complex.normSq ((c:ℂ)/3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedGaussCoefficient b c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hf,←mul_assoc]
  congr 1
  have hN : norm c≠0 := (norm_pos_of_ne_zero hc0).ne'
  have hN3 : norm (3*c)=9*norm c := by
    rw [norm_mul_eq]
    congr 1
    norm_num [norm,Complex.normSq_ofReal,show ((3:Eisenstein):ℂ)=3 from rfl]
  rw [Complex.normSq_div,hN3]
  norm_num [Complex.normSq_ofReal]
  change (2/(((Real.sqrt 3:ℝ):ℂ)*(9*(norm c:ℂ))))*((norm c:ℂ)/9)=_
  have hNC : (norm c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN
  field_simp
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Mellin representation of the actual rows at a translated
inverted cusp, retaining their finite ramified character. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaShiftedGrid_row (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    (p : ℂ × ℝ) (s : ℂ) :
    (∑' d : Eisenstein, cubicThetaShiftedGridTerm b (c,d) p s)=cubicThetaShiftedRowSeries b c p s := by
  have hi : Function.Injective (fun a : Eisenstein => 3*a) :=
    fun a b h => mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) h
  have hs : Function.support (fun d => cubicThetaShiftedGridTerm b (c,d) p s) ⊆
      Set.range (fun a : Eisenstein => 3*a) := by
    intro d hd
    by_cases ht : (3:Eisenstein)∣d
    · obtain ⟨a,ha⟩ := ht
      exact ⟨a,ha.symm⟩
    · exact False.elim (hd (by simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,ht]))
  rw [←hi.tsum_eq hs]
  unfold cubicThetaShiftedRowSeries
  apply tsum_congr
  intro a
  exact cubicThetaShiftedGridTerm_triple b hc a p s

theorem cubicThetaEisenstein_shifted_rows (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' c : Eisenstein, if primary c then cubicThetaShiftedRowSeries b c p s else 0 := by
  rw [cubicThetaEisenstein_shifted_grid b hp,(cubicThetaShiftedGrid_summable b hp hs).tsum_prod]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · rw [ite_eq_left hc,cubicThetaShiftedGrid_row b hc]
  · simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,hc]

lemma cubicThetaShiftedRowWeight_norm_eq {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    ‖cubicThetaShiftedRowWeight b c u‖=‖cubicSymbol c (3*u)‖ := by
  rw [cubicThetaShiftedRowWeight_factor hc,norm_mul,norm_star]
  change ‖cubicThetaKubotaValue (cubicThetaCuspStep b u)‖*_= _
  rw [cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaShiftedRowRadius_summable {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun a : Eisenstein => ‖cubicThetaShiftedRowWeight b c a‖*
      (cubicThetaRowRadius c p (3*a))^(-s.re)) := by
  simpa only [cubicThetaShiftedRowWeight_norm_eq hc] using cubicThetaInvertedRowRadius_summable hc hp hs

theorem cubicThetaShiftedRow_mellin (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaShiftedCuspGaussianRow b c p.1 t := by
  have hscale : cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*∑' a : Eisenstein,
        cubicThetaShiftedRowWeight b c a*(cubicThetaRowRadius c p (3*a):ℂ)^(-s) := by
    unfold cubicThetaShiftedRowSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro a
    rw [cubicThetaRowRadius_complex_power (primary_ne_zero hc) hp]
    ring
  have hM := cubicTheta_laplace_tsum (fun a => cubicThetaShiftedRowWeight b c a)
    (fun a => cubicThetaRowRadius c p (3*a)) (fun a => cubicThetaRowRadius_pos c (3*a) hp)
    (show 0 < s.re by linarith) (cubicThetaShiftedRowRadius_summable hc b hp hs)
  rw [hscale,mul_left_comm,hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaShiftedCuspGaussianRow
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro a
  have he : Real.exp (-cubicThetaRowRadius c p (3*a)*t)=
      Real.exp (-p.2^2*t)*Real.exp (-t*‖p.1+3*(a:ℂ)/(c:ℂ)‖^2) := by
    rw [←Real.exp_add]
    congr 1
    unfold cubicThetaRowRadius
    rw [Complex.normSq_eq_norm_sq]
    change -(‖p.1+3*(a:ℂ)/(c:ℂ)‖^2+p.2^2)*t=_
    ring
  rw [he,Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inverted row Fourier expansion, with absolute integrated
summability proved before interchanging its heat integral and lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaShiftedWeightedHeat_summable {v : ℝ} (hv : 0<v) {s : ℂ}
    (hs : 1 < s.re) {c : Eisenstein} (hc : primary c) (b : Eisenstein) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaShiftedRowFourierCoefficient b c z h*
        cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t‖) := by
  have ht := (cubicThetaShiftedDualHeat_mass_summable hv hs).mul_left (Nat.card (Residues (3*c)):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [cubicThetaShiftedRowFourierCoefficient,norm_mul,Circle.norm_coe,mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaShiftedGaussCoefficient_norm hc b h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

lemma cubicThetaShiftedRowHeat_factor {t : ℝ} (ht : 0 < t) (v : ℝ) (s : ℂ) (h : Eisenstein) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp
        (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ)) =
      (Real.pi:ℂ)*cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  have hp : (t:ℂ)^(s-1)/(t:ℂ) = (t:ℂ)^(s-2) := by
    calc
      _ = (t:ℂ)^(s-1)/(t:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
        congr 1
        ring
  rw [Complex.ofReal_div]
  calc
    _ = (Real.pi:ℂ)*((t:ℂ)^(s-1)/(t:ℂ))*
        ((Real.exp (-v^2*t):ℂ)*
          (Real.exp (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℂ)) := by ring
    _ = _ := by
      rw [hp, ← Complex.ofReal_mul, ← Real.exp_add]
      unfold cubicThetaDualHeat cubicThetaShiftedRowHeatScale
      have he : -v^2*t + -4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h) =
          -v^2*t-(4*Real.pi^2*Complex.normSq (cubicThetaShiftedRowFrequency h))/t := by ring
      rw [he]
      ring

lemma cubicThetaShiftedRow_heat_poisson {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0<t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaShiftedCuspGaussianRow b c z t=
      (2*Real.pi/(81*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedRowFourierCoefficient b c z h*
          cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  rw [cubicThetaShiftedCuspGaussianRow_poisson hc b z ht]
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  have he := cubicThetaShiftedRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(81*Real.sqrt 3):ℂ)*(cubicThetaShiftedGaussCoefficient b c h*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ))))=_
  calc
    _ = (2/(81*Real.sqrt 3):ℂ)*cubicThetaShiftedRowFourierCoefficient b c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ))) := by
      unfold cubicThetaShiftedRowFourierCoefficient
      ring
    _ = _ := by rw [he]; ring

theorem cubicThetaShiftedRow_fourier (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(81*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaShiftedRowFourierCoefficient b c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1 < s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaShiftedRowFourierCoefficient b c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h=0
    · simp [hh]
    · exact (cubicThetaShiftedRowHeatScale_pos hh).le
  have hi := integral_tsum_of_summable_integral_norm hFi
    (cubicThetaShiftedWeightedHeat_summable hp hs1 hc b p.1)
  rw [cubicThetaShiftedRow_mellin b hc hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(81*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein,
          cubicThetaShiftedRowFourierCoefficient b c p.1 h*
            cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
      congr 1
      rw [←integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaShiftedRow_heat_poisson hc b p.1 p.2 s ht)
    _ = _ := by
      rw [←hi]
      simp only [integral_const_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute arithmetic and heat majorants for collecting the actual
inverted Fourier coefficients on their half-plane of convergence. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaShiftedFrequencyDirichlet_tsum (b h : Eisenstein) (s : ℂ) :
    cubicThetaShiftedFrequencyDirichlet b h s=
      ∑' c : Eisenstein, cubicThetaShiftedFrequencyTerm b s h c := by
  have hsup : Function.support (cubicThetaShiftedFrequencyTerm b s h) ⊆ {c | primary c} := by
    intro c hc
    by_contra hn
    change ¬primary c at hn
    exact hc (by simp [cubicThetaShiftedFrequencyTerm,hn])
  calc
    _ = ∑' c : CubicThetaPrimaryPart, cubicThetaShiftedFrequencyTerm b s h c.val := by
      apply tsum_congr
      intro c
      simp only [cubicThetaShiftedFrequencyTerm,ite_eq_left c.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaShiftedGaussCoefficient_norm_real {c : Eisenstein} (hc : primary c)
    (b h : Eisenstein) : ‖cubicThetaShiftedGaussCoefficient b c h‖≤9*norm c := by
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) (primary_ne_zero hc)
  have ht := cubicThetaShiftedGaussCoefficient_norm hc b h
  rw [residues_card h3c,normNat_cast,norm_mul_eq] at ht
  have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
  rwa [h3] at ht

lemma cubicThetaShiftedFrequencyTerm_bound (b : Eisenstein) (s : ℂ) (h c : Eisenstein) :
    ‖cubicThetaShiftedFrequencyTerm b s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : primary c
  · have hc0 := primary_ne_zero hc
    rw [cubicThetaShiftedFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc0)]
    simp only [Complex.neg_re]
    have hg : ‖cubicThetaShiftedGaussCoefficient b c h‖≤9*norm c := by
      exact cubicThetaShiftedGaussCoefficient_norm_real hc b h
    calc
      _ ≤ (9*norm c)*(norm c)^(-s.re) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg (norm_nonneg c) _)
      _ = _ := by
        have he : norm c*(norm c)^(-s.re)=(norm c)^(-(s.re-1)) := by
          calc
            _ = (norm c)^(1:ℝ)*(norm c)^(-s.re) := by rw [Real.rpow_one]
            _ = _ := by
              rw [←Real.rpow_add (norm_pos_of_ne_zero hc0)]
              congr 1
              ring
        rw [mul_assoc,he]
  · simp only [cubicThetaShiftedFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaShiftedFrequency_heat_norm_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaShiftedFrequencyTerm b s ch.2 ch.1*
        (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency ch.2)):ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale ch.2) t)‖) := by
  have hc := (summable_eisenstein_norm_rpow (show 1 < s.re-1 by linarith)).mul_left 9
  have hh := cubicThetaShiftedDualHeat_mass_summable hp (show 1 < s.re by linarith)
  have hprod : Summable (fun ch : Eisenstein × Eisenstein =>
      (9*(norm ch.1)^(-(s.re-1)))*
        (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale ch.2) t‖)) :=
    summable_mul_of_summable_norm hc.norm hh.norm
  apply hprod.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ch
  rw [norm_mul,norm_mul,Circle.norm_coe,mul_one]
  exact mul_le_mul (cubicThetaShiftedFrequencyTerm_bound b s ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collect the inverted Fourier coefficients by an absolutely
convergent interchange of the two actual lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_shifted_fourier_rows (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' c : Eisenstein, if primary c then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(81*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaShiftedRowFourierCoefficient b c p.1 h*
            (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)
        else 0 := by
  rw [cubicThetaEisenstein_shifted_rows b hp hs,←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simpa only [ite_eq_left hc] using cubicThetaShiftedRow_fourier b hc hp hs
  · simp only [ite_eq_right hc,mul_zero]

theorem cubicThetaEisenstein_shifted_fourier_coefficients (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      (2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaShiftedFrequencyTerm b s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaShiftedFrequency_heat_norm_summable b hp hs).of_norm
  have hswap : (∑' c,∑' h,F c h)=(∑' h,∑' c,F c h) := hF.tsum_comm.symm
  rw [cubicThetaEisenstein_shifted_fourier_rows b hp hs]
  calc
    _ = ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h,F c h) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : primary c
      · rw [ite_eq_left hc,cubicTheta_row_power hp (primary_ne_zero hc),
          ←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaShiftedFrequencyTerm,ite_eq_left hc,
          cubicThetaShiftedRowFourierCoefficient]
        ring
      · simp [F,cubicThetaShiftedFrequencyTerm,hc]
    _ = ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c,F c h) := by rw [hswap]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right,cubicThetaShiftedFrequencyDirichlet_tsum]

theorem cubicThetaEisenstein_shifted_fourier_normalized (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  apply mul_left_cancel₀ hG
  rw [cubicThetaEisenstein_shifted_fourier_coefficients b hp hs]
  field_simp

lemma cubicThetaShiftedFourierCoefficients_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun h : Eisenstein => cubicThetaShiftedFrequencyDirichlet b h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)) := by
  have h := (cubicThetaShiftedFrequency_heat_norm_summable b hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right,cubicThetaShiftedFrequencyDirichlet_tsum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual continuous Fourier expansion at a translated cusp,
parametrized by its period-nine torus. All frequencies, including zero,
are retained until the explicit arithmetic support is applied. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaShiftedFourierTerm_summable (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) : Summable (cubicThetaShiftedFourierTerm b v s) := by
  have he := cubicThetaShiftedFourierCoefficients_summable b (p:=(0,v)) hv hs
  change Summable (fun h => cubicThetaShiftedFrequencyDirichlet b h s*
    ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)
  simpa only [tracePair,zero_mul,Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,
    Circle.coe_one,mul_one] using he

lemma cubicThetaShiftedTorusSeries_summable (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) : Summable (fun h : Eisenstein =>
      cubicThetaShiftedFourierTerm b v s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaShiftedFourierTerm_summable b hv hs).norm

lemma cubicThetaShifted_frequency_cell (x : Fin 2 → ℝ) (h : Eisenstein) :
    tracePair (3*cubicThetaPeriodCell x) (cubicThetaShiftedRowFrequency h)=
      tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h) := by
  unfold tracePair cubicThetaShiftedRowFrequency cubicThetaRowFrequency
  congr 2
  ring

lemma cubicThetaShiftedTorusSeries_real (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (x : Fin 2 → ℝ) :
    cubicThetaShiftedTorusSeries b v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
        (Real.fourierChar (tracePair (3*cubicThetaPeriodCell x) (cubicThetaShiftedRowFrequency h)):ℂ)*
        ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaShiftedTorusSeries_summable b hv hs)
  change cubicThetaShiftedTorusSeries b v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaShiftedFourierTerm b v s h*cubicThetaTorusFourier h
    (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]
  unfold cubicThetaShiftedFourierTerm
  ring

lemma cubicThetaShiftedTorus_real (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (x : Fin 2 → ℝ) :
    cubicThetaShiftedTorus b v s (fun i => (x i:UnitAddCircle))=
      cubicThetaEisenstein
        ((cubicThetaInversion 1 (3*cubicThetaPeriodCell x,v)).1+b,
          (cubicThetaInversion 1 (3*cubicThetaPeriodCell x,v)).2) s := by
  rw [cubicThetaEisenstein_shifted_fourier_normalized b hv hs]
  simp only [cubicThetaShiftedTorus,ContinuousMap.smul_apply,smul_eq_mul,
    cubicThetaShiftedTorusSeries_real b hv hs]

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_6
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions_2
lemma cubicThetaShiftedTorusSeries_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaShiftedTorusSeries b v s)) k=cubicThetaShiftedFourierTerm b v s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaShiftedTorusSeries b v s)=_
  rw [cubicThetaShiftedTorusSeries,L.map_tsum (cubicThetaShiftedTorusSeries_summable b hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPeriodMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period-nine cell and its exact volume normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedHorizontalCell_compact_container :
    ∃ K : Set ℂ,IsCompact K ∧ cubicThetaShiftedHorizontalCell⊆K := by
  obtain ⟨K,hK,hcell⟩ := cubicThetaHorizontalCell_compact_container
  exact ⟨(fun z : ℂ => 3*z) '' K,hK.image (continuous_const.mul continuous_id),
    Set.image_mono hcell⟩

lemma cubicThetaShiftedPeriodEquiv_map_volume :
    Measure.map cubicThetaShiftedPeriodEquiv volume=
      ENNReal.ofReal (2/(81*Real.sqrt 3)) • (volume : Measure ℂ) := by
  have he : (cubicThetaShiftedPeriodEquiv : (Fin 2 → ℝ) → ℂ)=
      (fun z : ℂ => 3*z) ∘ cubicThetaPeriodEquiv := rfl
  rw [he,←Measure.map_map (by fun_prop) cubicThetaPeriodEquiv.continuous.measurable,
    cubicThetaPeriodEquiv_map_volume,Measure.map_smul,
    complexMul_map_volume 3 (by norm_num),smul_smul]
  congr 1
  norm_num only [Complex.normSq_ofNat,ENNReal.ofReal_ofNat]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cubicThetaShiftedPeriodEquiv_preimage_cell :
    cubicThetaShiftedPeriodEquiv ⁻¹' cubicThetaShiftedHorizontalCell=
      {x : Fin 2 → ℝ | ∀ i,x i∈Ico (0:ℝ) 1} := by
  have hinj : Function.Injective (fun z : ℂ => 3*z) :=
    fun _ _ h => mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) h
  change cubicThetaPeriodEquiv ⁻¹'
    ((fun z : ℂ => 3*z) ⁻¹' ((fun z : ℂ => 3*z) '' cubicThetaHorizontalCell))=_
  rw [Set.preimage_image_eq _ hinj,cubicThetaPeriodEquiv_preimage_cell]

lemma cubicThetaShiftedHorizontalCell_integral (f : ℂ → ℂ) :
    (∫ z in cubicThetaShiftedHorizontalCell,f z)=
      (81*Real.sqrt 3/2:ℝ) •
        ∫ x in {x : Fin 2 → ℝ | ∀ i,x i∈Ico (0:ℝ) 1},f (3*cubicThetaPeriodCell x) := by
  have hi := setIntegral_map_equiv (μ:=volume)
    cubicThetaShiftedPeriodEquiv.toHomeomorph.toMeasurableEquiv f cubicThetaShiftedHorizontalCell
  change (∫ z in cubicThetaShiftedHorizontalCell,f z ∂Measure.map cubicThetaShiftedPeriodEquiv volume)=
    ∫ x in cubicThetaShiftedPeriodEquiv ⁻¹' cubicThetaShiftedHorizontalCell,
      f (cubicThetaShiftedPeriodEquiv x) at hi
  rw [cubicThetaShiftedPeriodEquiv_map_volume,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(81*Real.sqrt 3)),
    cubicThetaShiftedPeriodEquiv_preimage_cell] at hi
  have he : (81*Real.sqrt 3/2:ℝ)*(2/(81*Real.sqrt 3))=1 := by field_simp
  calc
    _ = (81*Real.sqrt 3/2:ℝ) • ((2/(81*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaShiftedHorizontalCell,f z) := by rw [smul_smul,he,one_smul]
    _ = _ := congrArg (fun w : ℂ => (81*Real.sqrt 3/2:ℝ) • w) hi

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_7
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions_3
lemma cubicThetaShiftedHorizontalCoefficient (f : ℂ → ℂ)
    (F : C(UnitAddTorus (Fin 2),ℂ)) (h : Eisenstein)
    (hf : ∀ x,f (3*cubicThetaPeriodCell x)=F (fun i => (x i:UnitAddCircle))) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*f z)=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h := by
  rw [cubicThetaShiftedHorizontalCell_integral,cubicThetaTorusCoefficient_integral,
    cubicThetaTorus_integral_cell]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [hf,cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]

lemma cubicThetaShiftedTorus_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaShiftedTorus b v s)) h=
      ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaShiftedFourierTerm b v s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaShiftedTorus b v s)=_
  rw [cubicThetaShiftedTorus,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,
    cubicThetaShiftedTorusSeries_coefficient b hv hs,smul_eq_mul]

lemma cubicThetaShiftedPeriod_fourier_constant :
    ((81*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(81*Real.sqrt 3):ℂ)=(Real.pi:ℂ) := by
  push_cast
  field_simp

theorem cubicThetaShifted_horizontal_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        cubicThetaEisenstein ((cubicThetaInversion 1 (z,v)).1+b,
          (cubicThetaInversion 1 (z,v)).2) s)=
      ((Real.pi:ℂ)/Complex.Gamma s)*(v:ℂ)^s*cubicThetaShiftedFrequencyDirichlet b h s*
        ∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  rw [cubicThetaShiftedHorizontalCoefficient _ (cubicThetaShiftedTorus b v s) h
    (fun x => (cubicThetaShiftedTorus_real b hv hs x).symm),
    cubicThetaShiftedTorus_coefficient b hv hs,Complex.real_smul]
  unfold cubicThetaShiftedFourierTerm
  calc
    _ = (((81*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(81*Real.sqrt 3):ℂ))*
      ((v:ℂ)^s/Complex.Gamma s)*cubicThetaShiftedFrequencyDirichlet b h s*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t) := by ring
    _ = _ := by rw [cubicThetaShiftedPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact height windows in the actual period-nine cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedWindow_compact_container {a : ℝ} (ha : 0<a) (d : ℝ) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧ cubicThetaShiftedWindow a d⊆K ∧
      ∀ p∈K,a≤p.val.2 := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
  let B : Set (ℂ×ℝ) := L ×ˢ Icc a d
  have hpos : B⊆{y : ℂ×ℝ | 0<y.2} := fun y hy => ha.trans_le hy.2.1
  have hc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ×ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' B,
    (hL.prod isCompact_Icc).image_of_continuousOn (hc.mono hpos),?_,?_⟩
  · intro p hp
    refine ⟨p.val,⟨hcell hp.1,hp.2⟩,?_⟩
    exact cubicThetaPointInclusion.left_inv
      (by rw [cubicThetaPointInclusion_source]; trivial)
  · rintro p ⟨y,hy,rfl⟩
    have he := cubicThetaPointInclusion.right_inv
      (show y∈cubicThetaPointInclusion.target by
        rw [cubicThetaPointInclusion_target]; exact hpos hy)
    change (cubicThetaPointInclusion (cubicThetaPointInclusion.symm y)).2≥a
    rw [he]
    exact hy.2.1

lemma cubicThetaShiftedWindow_coordinates {a : ℝ} (ha : 0<a) (d : ℝ) :
    cubicThetaPointCoordinates '' cubicThetaShiftedWindow a d=
      cubicThetaShiftedHorizontalCell ×ˢ Icc a d := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hy
    refine ⟨⟨y,ha.trans_le hy.2.1⟩,hy,rfl⟩

lemma cubicThetaShiftedWindow_fubini {a : ℝ} (ha : 0<a) (d : ℝ)
    (f : ℂ×ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure) :
    (∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Icc a d,∫ z in cubicThetaShiftedHorizontalCell,f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density
    (cubicThetaShiftedWindow_measurable a d) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaShiftedWindow_measurable a d),
    cubicThetaShiftedWindow_coordinates ha d]
  rw [cubicThetaShiftedWindow_coordinates ha d] at hi
  change Integrable (fun y : ℂ×ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [←Measure.prod_restrict] at hi
  change (∫ y : ℂ×ℝ,f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaShiftedHorizontalCell ×ˢ Icc a d))=_
  rw [←Measure.prod_restrict]
  exact integral_prod_symm _ hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindowTest
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded Fourier tests on finite translated-cusp windows. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedWindowTest_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K)
    (R : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (f : CubicThetaPoint → ℂ)
    (hf : R=ᵐ[cubicThetaPointMeasure.restrict K] f) :
    IntegrableOn (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p)
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure := by
  classical
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaShiftedWindowTest h W a d hK) R
  have he : Integrable ((cubicThetaShiftedWindow a d).indicator
      (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p))
      (cubicThetaPointMeasure.restrict K) := by
    apply hi.congr
    filter_upwards [(cubicThetaShiftedWindowWeight_memLp h W a d hK).coeFn_toLp,hf]
      with p hp hfp
    change inner ℂ (((cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _) p) _=_
    rw [hp,hfp,RCLike.inner_apply]
    simp only [starRingEnd_apply]
    by_cases hm : p∈cubicThetaShiftedWindow a d
    · simp only [indicator_of_mem hm]; ring
    · simp only [indicator_of_notMem hm,star_zero,mul_zero]
  rw [integrable_indicator_iff (cubicThetaShiftedWindow_measurable a d)] at he
  simpa only [IntegrableOn,Measure.restrict_restrict (cubicThetaShiftedWindow_measurable a d),
    inter_eq_left.mpr hSK] using he

lemma cubicThetaShiftedWindowTest_pairing (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K)
    (R : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (f : CubicThetaPoint → ℂ)
    (hf : R=ᵐ[cubicThetaPointMeasure.restrict K] f) :
    inner ℂ (cubicThetaShiftedWindowTest h W a d hK) R=
      ∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*f p ∂cubicThetaPointMeasure := by
  classical
  rw [L2.inner_def]
  calc
    _ = ∫ p in K,(cubicThetaShiftedWindow a d).indicator
        (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p) p
        ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaShiftedWindowWeight_memLp h W a d hK).coeFn_toLp,hf]
        with p hp hfp
      change inner ℂ (((cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _) p) _=_
      rw [hp,hfp,RCLike.inner_apply]
      simp only [starRingEnd_apply]
      by_cases hm : p∈cubicThetaShiftedWindow a d
      · simp only [indicator_of_mem hm]; ring
      · simp only [indicator_of_notMem hm,star_zero,mul_zero]
    _ = _ := by
      rw [setIntegral_indicator (cubicThetaShiftedWindow_measurable a d),
        inter_eq_right.mpr hSK]

lemma cubicThetaShiftedWindowObservation_meromorphic (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaShiftedWindowObservation b h W a d hK) s :=
  cubicThetaCompactShiftedObservation_meromorphic b hK _ hs

lemma cubicThetaShiftedWindowObservation_residue (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaShiftedWindowObservation b h W a d hK s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
            (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
        ∂cubicThetaPointMeasure)) := by
  have ht := ((innerSL ℂ (cubicThetaShiftedWindowTest h W a d hK)).continuous.tendsto _).comp
    (cubicThetaCompactShiftedFamily_residue b hK)
  simp only [Function.comp_def,innerSL_apply_apply,inner_smul_right] at ht
  rw [cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
    (cubicThetaCompactShiftedResidue_model b hK)] at ht
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
    cubicThetaShiftedWindowObservation,cubicThetaCompactShiftedObservation] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFrequencyContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the actual translated-cusp Dirichlet coefficients through
the already proved primary family. No cusp transform is postulated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRegularizedShiftedFrequency_analytic (b : ℤ) {h : Eisenstein}
    (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedShiftedFrequency b h) {s : ℂ | 1 < s.re} := by
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · exact analyticOnNhd_const.mul
      (cubicThetaRegularizedPrimaryOne_analytic (mul_ne_zero lambdaE_prime.ne_zero hh))
  · exact analyticOnNhd_const

lemma cubicThetaRegularizedShiftedFrequency_right (a b : ℤ) {h : Eisenstein}
    (hh : h≠0) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedShiftedFrequency b h s=
      (s-4/3)*cubicThetaShiftedFrequencyDirichlet ((a:Eisenstein)+b*omegaE) h s := by
  rw [cubicThetaShiftedFrequencyDirichlet_eq]
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · rw [cubicThetaRegularizedPrimaryOne_right (mul_ne_zero lambdaE_prime.ne_zero hh) hs,
      ←cubicThetaPrimaryFourierSeries_two_shift]
    ring
  · simp only [mul_zero]

lemma cubicThetaRegularizedShiftedFrequency_pole (b : ℤ) {h : Eisenstein}
    (hh : h≠0) :
    cubicThetaRegularizedShiftedFrequency b h (4/3)=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3) else 0 := by
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · rw [cubicThetaRegularizedPrimaryOne_residue_eq (mul_ne_zero lambdaE_prime.ne_zero hh)]
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRadialMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire radial factors for the actual shifted frequency, including a
finite closed height window. The endpoint changes are null sets. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedRadial_height_dilation (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {v : ℝ} (hv : 0<v) (s : ℂ) :
    star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3=
    ∫ u in Ioi (0:ℝ),cubicThetaRadialMellinIntegrand W
      (cubicThetaShiftedRowHeatScale h) s (v,u) := by
  rw [show star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)/(v:ℂ)^3*((v:ℂ)^s*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)) by ring,
    cubicThetaHeat_height_dilation hv]
  calc
    _ = star (W v)/(v:ℂ)^2*
        ∫ u in Ioi (0:ℝ),(u:ℂ)^(s-2)*
          cubicThetaLinearHeat v (cubicThetaShiftedRowHeatScale h) u := by
      field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
    _ = _ := by
      rw [←integral_const_mul]
      congr 1
      ext u
      unfold cubicThetaRadialMellinIntegrand
      ring

lemma cubicThetaShiftedPositiveRadial_integrable {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    IntegrableOn (fun v => star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3)
      (Ioi ε) := by
  have hi := (cubicThetaPositiveRadialMellin_integrable W hε
    (cubicThetaShiftedRowHeatScale_pos hh) s).integral_prod_left
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaShiftedRadial_height_dilation h W (hε.trans hv) s).symm

lemma cubicThetaShiftedPositiveRadial_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaShiftedPositiveRadialTest h W ε s=
      mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaShiftedRowHeatScale h)) (s-1) := by
  unfold cubicThetaShiftedPositiveRadialTest
  calc
    _ = ∫ v in Ioi ε,∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaShiftedRowHeatScale h) s (v,u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact cubicThetaShiftedRadial_height_dilation h W (hε.trans hv) s
    _ = ∫ u in Ioi (0:ℝ),∫ v in Ioi ε,
        cubicThetaRadialMellinIntegrand W (cubicThetaShiftedRowHeatScale h) s (v,u) :=
      integral_integral_swap (cubicThetaPositiveRadialMellin_integrable W hε
        (cubicThetaShiftedRowHeatScale_pos hh) s)
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaPositiveAveragedHeat]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

lemma cubicThetaShiftedPositiveRadial_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    Differentiable ℂ (cubicThetaShiftedPositiveRadialTest h W ε) := by
  rw [show cubicThetaShiftedPositiveRadialTest h W ε=
    (fun s : ℂ => mellin (cubicThetaPositiveAveragedHeat W ε
      (cubicThetaShiftedRowHeatScale h)) (s-1)) from
        funext (cubicThetaShiftedPositiveRadial_mellin hh W hε)]
  exact (cubicThetaPositiveAveragedHeat_mellin_entire W hε
    (cubicThetaShiftedRowHeatScale_pos hh)).comp (differentiable_id.sub_const 1)

lemma cubicThetaShiftedWindowRadial_sub {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) (s : ℂ) :
    cubicThetaShiftedWindowRadialTest h W a d s=
      cubicThetaShiftedPositiveRadialTest h W a s-cubicThetaShiftedPositiveRadialTest h W d s := by
  unfold cubicThetaShiftedWindowRadialTest cubicThetaShiftedPositiveRadialTest
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le had,
    intervalIntegral.integral_Ioi_sub_Ioi
      (cubicThetaShiftedPositiveRadial_integrable hh W ha s) had]

lemma cubicThetaShiftedWindowRadial_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    Differentiable ℂ (cubicThetaShiftedWindowRadialTest h W a d) := by
  rw [show cubicThetaShiftedWindowRadialTest h W a d=
    (fun s => cubicThetaShiftedPositiveRadialTest h W a s-
      cubicThetaShiftedPositiveRadialTest h W d s) from
        funext (cubicThetaShiftedWindowRadial_sub hh W ha had)]
  exact (cubicThetaShiftedPositiveRadial_entire hh W ha).sub
    (cubicThetaShiftedPositiveRadial_entire hh W (ha.trans_le had))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedHorizontalContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual translated theta coefficient and its radial kernel. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaShiftedCell_integral_continuous
    {F : {v : ℝ // 0<v} → ℂ → ℂ} (hF : Continuous F.uncurry) :
    Continuous (fun v => ∫ z in cubicThetaShiftedHorizontalCell,F v z) := by
  let : LocallyCompactSpace {v : ℝ // 0<v} := isOpen_Ioi.locallyCompactSpace
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict cubicThetaShiftedHorizontalCell) :=
    isFiniteMeasure_restrict.mpr (by
      obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
      exact (lt_of_le_of_lt (measure_mono hcell) hL.measure_lt_top).ne)
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨U,hU,hUv⟩ := exists_compact_mem_nhds v
  obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
  obtain ⟨M,hM⟩ := (hU.prod hL).bddAbove_image hF.norm.continuousOn
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards with u
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine ⟨M,?_⟩
    filter_upwards [hUv] with u hu
    filter_upwards [ae_restrict_mem cubicThetaShiftedHorizontalCell_measurable] with z hz
    exact hM (mem_image_of_mem _ (show (u,z)∈U ×ˢ L from ⟨hu,hcell hz⟩))
  · filter_upwards with z
    exact (hF.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

lemma cubicThetaShiftedModelHorizontal_continuous (b h : Eisenstein) :
    ContinuousOn (cubicThetaShiftedModelHorizontal b h) (Ioi (0:ℝ)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply cubicThetaShiftedCell_integral_continuous
  change Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
    star (Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h)):ℂ)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (q.2,q.1.val)))
  have hc := (cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar).comp
    (continuous_const_smul (cubicThetaShiftedInversion b))
  have ht : Continuous (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
    simpa only [Function.comp_def,cubicThetaFullPointAction_apply] using hc
  have hp : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      (⟨(q.2,q.1.val),q.1.property⟩ : CubicThetaPoint)) :=
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have hchar : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  have he : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      star (Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h)):ℂ)) :=
    (continuous_subtype_val.comp hchar).star
  have hm : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (q.2,q.1.val))) :=
    (ht.comp hp).congr (fun _ => rfl)
  exact he.mul hm

lemma cubicThetaShiftedPoleRadial_height (h : Eisenstein) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedPoleRadial h v=
      (v:ℂ)*cubicThetaComplexHeightIntegral (4/3) (cubicThetaShiftedRowHeatScale h) v := by
  unfold cubicThetaShiftedPoleRadial
  rw [cubicThetaHeat_height_dilation hv,cubicThetaComplexHeightIntegral_real]

lemma cubicThetaShiftedPoleRadial_continuous {h : Eisenstein} (hh : h≠0) :
    ContinuousOn (cubicThetaShiftedPoleRadial h) (Ioi (0:ℝ)) := by
  intro v hv
  apply ContinuousWithinAt.congr_of_eventuallyEq
    ((Complex.continuous_ofReal.continuousAt.mul
      (((cubicThetaComplexHeightIntegral_analytic (4/3)
        (cubicThetaShiftedRowHeatScale_pos hh) (z:=(v:ℂ)) (by simpa using hv)).continuousAt).comp
          Complex.continuous_ofReal.continuousAt)).continuousWithinAt) ?_
    (cubicThetaShiftedPoleRadial_height h hv)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (cubicThetaShiftedPoleRadial_height h hu)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedResiduePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted height identities for the actual translated theta coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedModel_window_pairing (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) :
    (∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
      ∂cubicThetaPointMeasure)=
    ∫ v in Icc a d,star (W v)*cubicThetaShiftedModelHorizontal b h v/(v:ℂ)^3 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container ha d
  let f : ℂ×ℝ → ℂ := fun p => star (W p.2*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ))*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p)
  have hi : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure :=
    cubicThetaShiftedWindowTest_integrable h W a d hK hSK _ _
      (cubicThetaCompactShiftedResidue_model b hK)
  change (∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p)
    ∂cubicThetaPointMeasure)=_
  rw [cubicThetaShiftedWindow_fubini ha d f hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  dsimp only
  rw [cubicThetaShiftedModelHorizontal,←integral_const_mul,←integral_div]
  apply setIntegral_congr_fun cubicThetaShiftedHorizontalCell_measurable
  intro z _
  simp only [f,star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedConstantCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nontrivial translated cusps have zero constant coefficient. This is
deduced from the exact finite Gauss support, not assumed as a cusp condition. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShifted_nontrivial_constant (n : ℤ) (hn : ¬(3:ℤ) ∣ n) :
    ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein) := by
  rintro ⟨c,hc⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective c
  have hl : -lambdaE*(n:Eisenstein)=ofCoords (-n) (-2*n) := by
    unfold lambdaE ofCoords
    push_cast
    ring
  have hr : (3:Eisenstein)*ofCoords a b=ofCoords (3*a) (3*b) := by
    unfold ofCoords
    push_cast
    ring
  rw [hl,hr] at hc
  have hcoords := coordinates_unique (congrArg (fun z : Eisenstein => (z:ℂ)) hc)
  exact hn ⟨-a,by linarith [hcoords.1]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedModelPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual translated theta model has its proved nine-Eisenstein period. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaCuspTranslation_intertwines (b m : Eisenstein) :
    cubicThetaCuspTranslationMatrix b m*cubicThetaShiftedInversion b=
      cubicThetaShiftedInversion b*(cubicThetaPrincipalTranslation (3*m)).val := by
  apply Subtype.ext
  change (!![1-9*b*m,9*b^2*m;-9*m,1+9*b*m] : Matrix (Fin 2) (Fin 2) Eisenstein)*
      !![b,-1;1,0]=!![b,-1;1,0]*!![1,3*(3*m);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem cubicThetaShiftedModel_periodic (b m : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
        (p.val.1+9*(m:ℂ),p.val.2))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val) := by
  have he := cubicThetaArithmeticModel_automorphy (cubicThetaCuspTranslation b m)
    (cubicThetaShiftedInversion b • p)
  rw [cubicThetaCuspTranslation_value,one_mul] at he
  have ht : (cubicThetaCuspTranslation b m).val • (cubicThetaShiftedInversion b • p)=
      cubicThetaShiftedInversion b • ((cubicThetaPrincipalTranslation (3*m)).val • p) := by
    rw [←mul_smul,←mul_smul]
    change (cubicThetaCuspTranslationMatrix b m*cubicThetaShiftedInversion b) • p=_
    rw [cubicThetaCuspTranslation_intertwines]
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (((cubicThetaCuspTranslation b m).val • (cubicThetaShiftedInversion b • p)).val)=_ at he
  rw [ht,cubicThetaFullPointAction_apply] at he
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
      (cubicThetaPointCoordinates (cubicThetaPrincipalTranslation (3*m) • p)))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val) at he
  rw [cubicThetaPrincipalTranslation_coordinates] at he
  have hs : p.val.1+3*((3*m:Eisenstein):ℂ)=p.val.1+9*(m:ℂ) := by
    rw [Subalgebra.coe_mul,show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
    ring
  simpa only [cubicThetaPointCoordinates,hs] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWhittaker
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual translated-cusp coefficients in the fixed Whittaker normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedPoleHeat_whittaker {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaShiftedRowHeatScale h) t)=
      ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ)*
        cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v) := by
  let A := cubicThetaShiftedRowHeatScale h
  let q := ‖cubicThetaShiftedRowFrequency h‖
  have hA : 0<A := cubicThetaShiftedRowHeatScale_pos hh
  have hq : 0<q := norm_pos_iff.mpr (by
    change (h:ℂ)/(9*traceLambda)≠0
    exact div_ne_zero (fun hz => hh (Subtype.ext hz)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  have hI : (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=
      ((A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ):ℝ):ℂ)*(cubicBesselKernel (A*v^2):ℂ) := by
    rw [← cubicTheta_cubicPole_heat hA hv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    dsimp only [cubicThetaDualHeat]
    rw [show (4/3:ℂ)-2=((-2/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow ht.le]
  have hx : (2*Real.pi*(q*v))^2=A*v^2 := by
    dsimp [A,q,cubicThetaShiftedRowHeatScale]
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hd : (A*v^2)^(1/6:ℝ)=A^(1/6:ℝ)*v^(1/3:ℝ) := by
    rw [Real.mul_rpow hA.le (sq_nonneg v),← Real.rpow_natCast v 2,← Real.rpow_mul hv.le]
    norm_num
  have ha : A^(1/3:ℝ)=A^(1/6:ℝ)*A^(1/6:ℝ) := by
    rw [← Real.rpow_add hA]
    norm_num
  have hpow : v^(4/3:ℝ)=v*v^(1/3:ℝ) := by
    rw [show (4/3:ℝ)=1+1/3 by norm_num,Real.rpow_add hv,Real.rpow_one]
  have hr : v^(4/3:ℝ)*(A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ))=
      (2*A^(1/6:ℝ)/q)*(q*v/2) := by
    rw [hd,ha,hpow]
    field_simp
  change (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=_
  rw [hI,show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow hv.le]
  change _=((2*A^(1/6:ℝ)/q:ℝ):ℂ)*cubicThetaWhittaker (q*v)
  rw [cubicThetaWhittaker,hx]
  rw [← mul_assoc, ← Complex.ofReal_mul, hr]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCoefficientNormalization
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The other-cusp Whittaker coefficients have the explicit arithmetic
normalization, with the same actual scalar as the original cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedFrequency_lambda (h : Eisenstein) :
    cubicThetaRowFrequency (lambdaE*h)=
      (3*traceLambda)*cubicThetaShiftedRowFrequency h := by
  unfold cubicThetaRowFrequency cubicThetaShiftedRowFrequency
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]
  ring

lemma cubicThetaShiftedPoleWeight {h : Eisenstein} (hh : h≠0) :
    2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖=
      3*(2*(cubicThetaRowHeatScale (lambdaE*h))^(1/6:ℝ)/
        ‖cubicThetaRowFrequency (lambdaE*h)‖) := by
  have hl : ‖traceLambda‖=Real.sqrt 3 := by
    apply (sq_eq_sq₀ (_root_.norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [←Complex.normSq_eq_norm_sq,traceLambda_normSq,Real.sq_sqrt (by norm_num)]
  have hq : ‖cubicThetaRowFrequency (lambdaE*h)‖=
      3*Real.sqrt 3*‖cubicThetaShiftedRowFrequency h‖ := by
    rw [cubicThetaShiftedFrequency_lambda,norm_mul,norm_mul,Complex.norm_ofNat,hl]
  have hA : cubicThetaRowHeatScale (lambdaE*h)=27*cubicThetaShiftedRowHeatScale h := by
    unfold cubicThetaRowHeatScale cubicThetaShiftedRowHeatScale
    rw [cubicThetaShiftedFrequency_lambda,Complex.normSq_mul,Complex.normSq_mul,
      traceLambda_normSq]
    norm_num
    ring
  have h27 : (27:ℝ)^(1/6:ℝ)=Real.sqrt 3 := by
    calc
      _ = ((3:ℝ)^3)^(1/6:ℝ) := by norm_num
      _ = (3:ℝ)^((3:ℝ)*(1/6:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
        norm_num
      _ = (3:ℝ)^(1/2:ℝ) := by norm_num
      _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have hn : ‖cubicThetaShiftedRowFrequency h‖≠0 := norm_ne_zero_iff.mpr (by
    unfold cubicThetaShiftedRowFrequency
    exact div_ne_zero (fun hz => hh (Subtype.ext hz)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  rw [hA,Real.mul_rpow (by norm_num) (cubicThetaShiftedRowHeatScale_pos hh).le,h27,hq]
  field_simp

theorem cubicThetaShiftedNormalizedCoefficient_explicit (n : ℤ) {h : Eisenstein} (hh : h≠0) :
    cubicThetaShiftedNormalizedCoefficient n h=
      if (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) then
        3*cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (3*h) else 0 := by
  unfold cubicThetaShiftedNormalizedCoefficient cubicThetaShiftedResidueFactor
  rw [cubicThetaRegularizedShiftedFrequency_pole n hh]
  split_ifs with hs
  · rw [cubicThetaShiftedPoleWeight hh,Complex.ofReal_mul,Complex.ofReal_ofNat]
    have he := cubicThetaCoefficientScalar (mul_ne_zero lambdaE_prime.ne_zero hh)
    have hi : -lambdaE*(lambdaE*h)=3*h := by
      rw [←mul_assoc,neg_mul,←pow_two,lambdaE_sq]
      ring
    rw [hi] at he
    rw [mul_assoc (3:ℂ) cubicThetaArithmeticBaseScalar,←he]
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    push_cast
    field_simp
    ring
  · simp only [mul_zero,zero_mul,zero_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedModelSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolutely convergent arithmetic series determined by the proved
other-cusp coefficients. Its constant coefficient is explicitly zero. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedFrequency_third (h : Eisenstein) :
    cubicThetaShiftedRowFrequency h=cubicThetaRowFrequency h/3 := by
  unfold cubicThetaShiftedRowFrequency cubicThetaRowFrequency
  field_simp [traceLambda_ne_zero]
  ring

lemma cubicThetaShiftedNormalizedCoefficient_bound (n : ℤ) {h : Eisenstein} (hh : h≠0) :
    ‖cubicThetaShiftedNormalizedCoefficient n h‖≤243*‖cubicThetaArithmeticBaseScalar‖ := by
  rw [cubicThetaShiftedNormalizedCoefficient_explicit n hh]
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_ofNat]
    calc
      _ ≤ (3*‖cubicThetaArithmeticBaseScalar‖)*81 :=
        mul_le_mul_of_nonneg_left (cubicThetaArithmeticCoefficient_norm_le _)
          (mul_nonneg (by norm_num) (_root_.norm_nonneg _))
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

lemma cubicThetaShiftedBareTerm_summable {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaShiftedBareTerm v) := by
  have hc : ∀ k : Eisenstein,k≠0 → ‖(1:ℂ)‖≤1*norm k := by
    intro k hk
    simpa only [norm_one,one_mul] using one_le_norm hk
  have hs := (cubicThetaSeries_summable (by norm_num : (0:ℝ)≤1) hc
    (div_pos hv (by norm_num : (0:ℝ)<3)) (0:ℂ)).comp_injective cubicThetaRowIndex_injective
  apply hs.congr
  intro h
  by_cases hh : h=0
  · simp [hh,cubicThetaSeriesTerm,cubicThetaShiftedBareTerm]
  · have hn := mul_ne_zero (neg_ne_zero.mpr lambdaE_prime.ne_zero) hh
    simp only [Function.comp_def,cubicThetaSeriesTerm,ite_eq_right hn,one_mul,
      cubicThetaShiftedBareTerm,ite_eq_right hh,cubicThetaRowFrequency_index,
      tracePair,mul_zero,Complex.zero_re,AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    rw [cubicThetaShiftedFrequency_third,norm_div,Complex.norm_ofNat]
    congr 1
    ring

lemma cubicThetaShiftedModelTerm_summable (n : ℤ) {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaShiftedModelTerm n v) := by
  have hs := ((cubicThetaShiftedBareTerm_summable hv).norm).mul_left
    (243*‖cubicThetaArithmeticBaseScalar‖)
  apply Summable.of_norm_bounded hs
  intro h
  by_cases hh : h=0
  · simp only [hh,cubicThetaShiftedModelTerm,cubicThetaShiftedBareTerm,ite_true, if_true,norm_zero,mul_zero,le_refl]
  · simp only [cubicThetaShiftedModelTerm,cubicThetaShiftedBareTerm,ite_eq_right hh,norm_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaShiftedNormalizedCoefficient_bound n hh)
      (_root_.norm_nonneg _)

lemma cubicThetaShiftedModelTorus_summable (n : ℤ) {v : ℝ} (hv : 0<v) :
    Summable (fun h : Eisenstein => cubicThetaShiftedModelTerm n v h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaShiftedModelTerm_summable n hv).norm

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_8
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions_4
lemma cubicThetaShiftedModelTorus_coefficient (n : ℤ) {v : ℝ} (hv : 0<v) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaShiftedModelTorus n v)) k=
      cubicThetaShiftedModelTerm n v k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaShiftedModelTorus n v)=_
  rw [cubicThetaShiftedModelTorus,L.map_tsum (cubicThetaShiftedModelTorus_summable n hv),
    tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_eq_right hne.symm,
      smul_zero]

lemma cubicThetaShiftedModelTorus_real (n : ℤ) {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaShiftedModelTorus n v (fun i => (x i:UnitAddCircle))=
      cubicThetaShiftedModelSeries n (3*cubicThetaPeriodCell x) v := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaShiftedModelTorus_summable n hv)
  change cubicThetaShiftedModelTorus n v (fun i => (x i:UnitAddCircle))=_ at he
  rw [he,cubicThetaShiftedModelSeries]
  apply tsum_congr
  intro h
  change cubicThetaShiftedModelTerm n v h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedSeriesFunction
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous periodic function given by the other-cusp arithmetic series. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPeriodCell_coordinates (z : ℂ) :
    cubicThetaPeriodCell (cubicThetaPeriodCoordinates z)=z := by
  unfold cubicThetaPeriodCell cubicThetaPeriodCoordinates
  rw [ContinuousLinearEquiv.apply_symm_apply]
  field_simp

lemma cubicThetaShiftedModelSeries_torus (n : ℤ) {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaShiftedModelSeries n (3*z) v=
      cubicThetaShiftedModelTorus n v
        (fun i => (cubicThetaPeriodCoordinates z i:UnitAddCircle)) := by
  have he := cubicThetaShiftedModelTorus_real n hv (cubicThetaPeriodCoordinates z)
  rw [cubicThetaPeriodCell_coordinates] at he
  exact he.symm

lemma cubicThetaShiftedModelSeries_continuous (n : ℤ) {v : ℝ} (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaShiftedModelSeries n (3*z) v) := by
  simp_rw [cubicThetaShiftedModelSeries_torus n hv]
  apply (cubicThetaShiftedModelTorus n v).continuous.comp
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1:ℝ)).comp
    ((continuous_apply i).comp cubicThetaPeriodCoordinates_continuous)

lemma cubicThetaShifted_phase_tripled (z : ℂ) (h : Eisenstein) :
    (Real.fourierChar (tracePair (3*z) (cubicThetaShiftedRowFrequency h)):ℂ)=
      cubicThetaHorizontalCharacter h z := by
  unfold cubicThetaHorizontalCharacter
  apply congrArg (fun t : ℝ => (Real.fourierChar t:ℂ))
  rw [cubicThetaShiftedFrequency_third]
  exact congrArg (fun w : ℂ => 2*w.re) (by ring)

lemma cubicThetaShiftedModelSeries_periodic (n : ℤ) (v : ℝ) (m : Eisenstein) (z : ℂ) :
    cubicThetaShiftedModelSeries n (3*(z+3*(m:ℂ))) v=
      cubicThetaShiftedModelSeries n (3*z) v := by
  unfold cubicThetaShiftedModelSeries
  apply tsum_congr
  intro h
  rw [cubicThetaShifted_phase_tripled,cubicThetaShifted_phase_tripled,
    cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaShifted_actual_continuous (b : Eisenstein) {v : ℝ} (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*z,v))) := by
  have hp : Continuous (fun z : ℂ => (⟨(3*z,v),hv⟩ : CubicThetaPoint)) :=
    ((continuous_const.mul continuous_id).prodMk continuous_const).subtype_mk _
  have hc := (cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar).comp
    (continuous_const_smul (cubicThetaShiftedInversion b))
  have ht : Continuous (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
    simpa only [Function.comp_def,cubicThetaFullPointAction_apply] using hc
  exact (ht.comp hp).congr (fun _ => rfl)

lemma cubicThetaShifted_actual_periodic (b m : Eisenstein) {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*(z+3*(m:ℂ)),v))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*z,v)) := by
  have he := cubicThetaShiftedModel_periodic b m (⟨(3*z,v),hv⟩ : CubicThetaPoint)
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
      (3*z+9*(m:ℂ),v))=_ at he
  rw [show 3*z+9*(m:ℂ)=3*(z+3*(m:ℂ)) by ring] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedSeriesIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconstruction of the actual translated-cusp section from its computed
coefficients. The nontrivial cusp has no constant mode. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedCell_integral_scaled (f : ℂ → ℂ) :
    (∫ z in cubicThetaShiftedHorizontalCell,f z)=
      (9:ℝ) • ∫ z in cubicThetaHorizontalCell,f (3*z) := by
  rw [cubicThetaShiftedHorizontalCell_integral,cubicThetaHorizontalCell_integral,smul_smul]
  congr 1
  ring

local instance instMeasureSpaceUnitAddCircle_solutions_9_rda9fe9_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_5_rda9fe9_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma cubicThetaShiftedModelSeries_coefficient (n : ℤ) {v : ℝ} (hv : 0<v) (h : Eisenstein) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        cubicThetaShiftedModelSeries n z v)=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaShiftedModelTerm n v h := by
  rw [cubicThetaShiftedHorizontalCoefficient _ (cubicThetaShiftedModelTorus n v) h
    (fun x => (cubicThetaShiftedModelTorus_real n hv x).symm),
    cubicThetaShiftedModelTorus_coefficient n hv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual automorphic function by its nonzero Fourier
coefficient. Its constant coefficient is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNormalizedSeriesSection_apply (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val p=
      cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val=_
  unfold cubicThetaArithmeticModel cubicThetaSeriesConstant
  push_cast
  field_simp [cubicThetaArithmeticBaseScalar_ne_zero]

theorem cubicThetaNormalizedSeriesSection_inversion (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullInversion • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=_
  rw [cubicThetaArithmeticModel_inversion]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the translated-cusp coefficients on the common lambda^-4 lattice.
The congruence restriction forces the apparent larger lattice to collapse. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShifted_support_lambda {n h : Eisenstein}
    (hh : (3:Eisenstein) ∣ h-lambdaE*n) : lambdaE ∣ h := by
  have ht : lambdaE ∣ (3:Eisenstein) := ⟨-lambdaE,by
    rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
  have ha := dvd_add (dvd_trans ht hh) (dvd_mul_right lambdaE n)
  simpa only [sub_add_cancel] using ha

lemma cubicThetaShifted_support_cancel (n k : Eisenstein) :
    (3:Eisenstein) ∣ lambdaE*k-lambdaE*n ↔ lambdaE ∣ k-n := by
  rw [←mul_sub]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨-a,?_⟩
    apply mul_left_cancel₀ lambdaE_prime.ne_zero
    rw [ha]
    rw [show lambdaE*(lambdaE*(-a))= -(lambdaE^2)*a by ring,lambdaE_sq]
    ring
  · rintro ⟨a,ha⟩
    refine ⟨-a,?_⟩
    rw [ha,←mul_assoc,←pow_two,lambdaE_sq]
    ring

lemma cubicThetaShiftedFrequency_common (k : Eisenstein) :
    cubicThetaShiftedRowFrequency (lambdaE*k)=cubicThetaFrequency k := by
  rw [cubicThetaFrequency_div_nine]
  unfold cubicThetaShiftedRowFrequency
  rw [Subalgebra.coe_mul,lambdaE_coe]
  field_simp [traceLambda_ne_zero]

lemma cubicThetaShiftedNormalizedCoefficient_common (n : ℤ) {k : Eisenstein} (hk : k≠0) :
    cubicThetaShiftedNormalizedCoefficient n (lambdaE*k)=
      cubicThetaArithmeticBaseScalar*cubicThetaShiftedLatticeCoefficient n k := by
  rw [cubicThetaShiftedNormalizedCoefficient_explicit n (mul_ne_zero lambdaE_prime.ne_zero hk),
    cubicThetaShifted_support_cancel]
  unfold cubicThetaShiftedLatticeCoefficient
  split_ifs <;> ring

lemma cubicThetaShiftedModelTerm_support (n : ℤ) (z : ℂ) (v : ℝ) :
    Function.support (fun h => cubicThetaShiftedModelTerm n v h*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)) ⊆
        Set.range (fun k : Eisenstein => lambdaE*k) := by
  intro h hh
  change cubicThetaShiftedModelTerm n v h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)≠0 at hh
  have hz : h≠0 := by
    rintro rfl
    exact hh (by simp only [cubicThetaShiftedModelTerm,ite_true, if_true,zero_mul])
  have hs : (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) := by
    by_contra hn
    exact hh (by simp only [cubicThetaShiftedModelTerm,ite_eq_right hz,
      cubicThetaShiftedNormalizedCoefficient_explicit n hz,ite_eq_right hn,zero_mul])
  obtain ⟨k,hk⟩ := cubicThetaShifted_support_lambda hs
  exact ⟨k,hk.symm⟩

lemma cubicThetaShiftedModelTerm_common (n : ℤ) (z : ℂ) (v : ℝ) (k : Eisenstein) :
    cubicThetaShiftedModelTerm n v (lambdaE*k)*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency (lambdaE*k))):ℂ)=
        cubicThetaArithmeticBaseScalar*cubicThetaSeriesTerm
          (cubicThetaShiftedLatticeCoefficient n) z v k := by
  by_cases hk : k=0
  · subst k
    simp only [mul_zero,cubicThetaShiftedModelTerm,cubicThetaSeriesTerm,ite_true, if_true,zero_mul]
  · simp only [cubicThetaShiftedModelTerm,cubicThetaSeriesTerm,
      ite_eq_right (mul_ne_zero lambdaE_prime.ne_zero hk),ite_eq_right hk,
      cubicThetaShiftedNormalizedCoefficient_common n hk,cubicThetaShiftedFrequency_common]
    have ht : tracePair z (cubicThetaFrequency k)=tracePair (cubicThetaFrequency k) z := by
      exact congrArg (fun w : ℂ => 2*w.re) (mul_comm z (cubicThetaFrequency k))
    rw [ht]
    ring

theorem cubicThetaShiftedModelSeries_common (n : ℤ) (z : ℂ) (v : ℝ) :
    cubicThetaShiftedModelSeries n z v=cubicThetaArithmeticBaseScalar*
      cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) (z,v) := by
  have hinj : Function.Injective (fun k : Eisenstein => lambdaE*k) :=
    fun _ _ he => mul_left_cancel₀ lambdaE_prime.ne_zero he
  have he := hinj.tsum_eq (cubicThetaShiftedModelTerm_support n z v)
  rw [cubicThetaShiftedModelSeries,←he]
  simp_rw [cubicThetaShiftedModelTerm_common]
  exact tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveHeightSeparation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact windows separate continuous functions at every positive height. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveHeightWindow_separates {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi (0:ℝ)))
    (hz : ∀ (W : C_c(ℝ,ℂ)) (a d : ℝ),0<a → a≤d →
      (∫ t in Icc a d,star (W t)*F t)=0) {v : ℝ} (hv : 0<v) : F v=0 := by
  let a := v/2
  let d := v+1
  have ha : 0<a := by dsimp [a]; linarith
  have hvi : v∈Ioo a d := by dsimp [a,d]; constructor <;> linarith
  have hc : ContinuousOn F (Ioo a d) := hF.mono (fun t ht => lt_trans ha ht.1)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),t∈Ioo a d → F t=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn measurableSet_Ioo)
    intro g hg hgc hgs
    let W : C_c(ℝ,ℂ) :=
      ⟨⟨fun t => (g t:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
        hgc.comp_left Complex.ofReal_zero⟩
    have he : (∫ t : ℝ,g t • F t)=∫ t in Icc a d,g t • F t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g t=0 := image_eq_zero_of_notMem_tsupport
        (fun hs => ht ⟨(hgs hs).1.le,(hgs hs).2.le⟩)
      rw [hg0,zero_smul]
    rw [he]
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using
        hz W a d ha (le_trans hvi.1.le hvi.2.le)
  have hae' : F=ᵐ[volume.restrict (Ioo a d)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hae] with t ht he
    exact he ht
  exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hc continuousOn_const hvi


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactIncomingTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire compact incoming corrections after the actual integral Mobius action.
This permits residue observations at every positive height. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCompactIncomingTransform_differentiable
    (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (f : CubicThetaPoint → ℂ)
    (hf : IntegrableOn f K cubicThetaPointMeasure) :
    Differentiable ℂ (fun s : ℂ => ∫ p in K,f p*
      cubicThetaIncomingEisenstein (δ • p).val s ∂cubicThetaPointMeasure) := by
  have hmap : Continuous (fun p : CubicThetaPoint => (δ • p).val) :=
    continuous_subtype_val.comp (continuous_const_smul δ)
  have hKC := hK.image hmap
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hKC
    (by rintro _ ⟨p,_,rfl⟩; exact (δ • p).property)
  have hterm (r : CubicThetaBottomRow) : Differentiable ℂ (fun s : ℂ => ∫ p in K,
      f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure) := by
    have hi := hf.mul_continuousOn
      ((cubicThetaIncomingTerm_point_continuous r 0).comp (continuous_const_smul δ)).continuousOn hK
    have hd := cubicThetaCompactExponential_differentiable hK _ hi
      (fun p => Real.log (r.height (δ • p).val))
      ((cubicThetaRowLogHeight_point_continuous r).comp (continuous_const_smul δ)).continuousOn
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    apply setIntegral_congr_fun hK.measurableSet
    intro p _
    change f p*cubicThetaIncomingTerm r (δ • p).val s=
      f p*cubicThetaIncomingTerm r (δ • p).val 0*
        Complex.exp (s*(Real.log (r.height (δ • p).val):ℂ))
    rw [cubicThetaIncomingTerm_exponential r (δ • p) s]
    ring
  have he (s : ℂ) : (∫ p in K,f p*
      cubicThetaIncomingEisenstein (δ • p).val s ∂cubicThetaPointMeasure)=
      ∑ r∈S,∫ p in K,f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure := by
    calc
      _ = ∫ p in K,∑ r∈S,f p*cubicThetaIncomingTerm r (δ • p).val s
          ∂cubicThetaPointMeasure := by
        apply setIntegral_congr_fun hK.measurableSet
        intro p hp
        change f p*cubicThetaIncomingEisenstein (δ • p).val s=
          ∑ r∈S,f p*cubicThetaIncomingTerm r (δ • p).val s
        rw [hS (δ • p).val ⟨p,hp,rfl⟩ s,Finset.mul_sum]
      _ = _ := integral_finsetSum S (fun r _ => hf.mul_continuousOn
        ((cubicThetaIncomingTerm_point_continuous r s).comp (continuous_const_smul δ)).continuousOn hK)
  rw [show (fun s : ℂ => ∫ p in K,f p*cubicThetaIncomingEisenstein (δ • p).val s
      ∂cubicThetaPointMeasure)=(fun s => ∑ r∈S,∫ p in K,
      f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure) from funext he]
  exact Differentiable.fun_sum (fun r _ => hterm r)

lemma cubicThetaShiftedIncomingWindow_differentiable (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∫ p in cubicThetaShiftedWindow a d,
      star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s
        ∂cubicThetaPointMeasure) := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container ha d
  let : IsFiniteMeasure (cubicThetaPointMeasure.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let f := (cubicThetaShiftedWindow a d).indicator
    (fun p => star (cubicThetaShiftedFourierWeight h W p))
  have hf : IntegrableOn f K cubicThetaPointMeasure := by
    have hm := (cubicThetaShiftedWindowWeight_memLp h W a d hK).star.integrable (by norm_num)
    apply hm.congr
    filter_upwards with p
    change star ((cubicThetaShiftedWindow a d).indicator
      (cubicThetaShiftedFourierWeight h W) p)=f p
    dsimp only [f]
    by_cases hp : p∈cubicThetaShiftedWindow a d
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp,star_zero]
  have hd := cubicThetaCompactIncomingTransform_differentiable
    (cubicThetaShiftedInversion b) hK f hf
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  calc
    _ = ∫ p in K,(cubicThetaShiftedWindow a d).indicator
        (fun p => star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s) p
          ∂cubicThetaPointMeasure := by
      rw [setIntegral_indicator (cubicThetaShiftedWindow_measurable a d),inter_eq_right.mpr hSK]
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p _
      exact Set.indicator_mul_left _ _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFullObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full translated-cusp observation, including the entire incoming
correction at low height. Its residue is unchanged. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCompactShiftedFamily_remainder (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCompactShiftedFamily b hK s=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => cubicThetaResidueScale*cubicThetaArithmeticRemainder
        (cubicThetaShiftedInversion b • p).val s) := by
  have hF := cubicThetaCompactIntegralRestriction_section (cubicThetaShiftedInversion b) hK
    (cubicThetaArithmeticSection s (by linarith)) (cubicThetaArithmeticSection_memLp hs)
  have hscalar := Lp.coeFn_smul cubicThetaResidueScale
    (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
      ((cubicThetaArithmeticSection_memLp hs).toLp _))
  rw [cubicThetaCompactShiftedFamily,map_smul,←cubicThetaArithmeticL2_eq_forcedResolvent hs]
  dsimp only [cubicThetaArithmeticL2]
  filter_upwards [hscalar,hF] with p hp hFp
  rw [hp]
  change cubicThetaResidueScale*_= _
  rw [hFp]
  rfl

lemma cubicThetaShiftedFullObservation_meromorphic (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaShiftedFullObservation b h W a d hK) s :=
  (cubicThetaShiftedWindowObservation_meromorphic b h W a d hK hs).add
    ((analyticAt_const.mul ((cubicThetaShiftedIncomingWindow_differentiable b h W ha d).analyticAt s)).meromorphicAt)

lemma cubicThetaShiftedIncomingWindow_integrable (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) (s : ℂ) :
    IntegrableOn (fun p => star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s)
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure := by
  have hc := (cubicThetaShiftedFourierWeight_continuous h W).star.mul
    ((cubicThetaIncoming_point_continuous s).comp
      (continuous_const_smul (cubicThetaShiftedInversion b)))
  exact (hc.continuousOn.integrableOn_compact hK).mono_set hSK

lemma cubicThetaShiftedFullObservation_right (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaShiftedFullObservation b h W a d hK s=
      cubicThetaResidueScale*∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s
          ∂cubicThetaPointMeasure := by
  have hR := cubicThetaShiftedWindowTest_integrable h W a d hK hSK _ _
    (cubicThetaCompactShiftedFamily_remainder b hK hs)
  have hI := (cubicThetaShiftedIncomingWindow_integrable b h W a d hK hSK s).const_mul
    cubicThetaResidueScale
  rw [cubicThetaShiftedFullObservation,cubicThetaShiftedWindowObservation,
    cubicThetaCompactShiftedObservation,cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
      (cubicThetaCompactShiftedFamily_remainder b hK hs),cubicThetaShiftedIncomingWindow,
    ←integral_const_mul,←integral_add hR hI,←integral_const_mul]
  apply setIntegral_congr_fun (cubicThetaShiftedWindow_measurable a d)
  intro p _
  dsimp only
  change star (cubicThetaShiftedFourierWeight h W p)*
      (cubicThetaResidueScale*(cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s-
        cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s))+
      cubicThetaResidueScale*(star (cubicThetaShiftedFourierWeight h W p)*
        cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s)=_
  ring

lemma cubicThetaShiftedFullObservation_residue (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaShiftedFullObservation b h W a d hK s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
            (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
          ∂cubicThetaPointMeasure)) := by
  have hzero : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hc : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hi := (cubicThetaShiftedIncomingWindow_differentiable b h W ha d).continuous
    |>.continuousAt (x:=(4/3:ℂ))
  have hc : ContinuousAt (fun s : ℂ => cubicThetaResidueScale*
      cubicThetaShiftedIncomingWindow b h W a d s) (4/3:ℂ) := continuousAt_const.mul hi
  have hz := hzero.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := (cubicThetaShiftedWindowObservation_residue b h W a d hK hSK).add hz
  simpa only [cubicThetaShiftedFullObservation,cubicThetaShiftedIncomingWindow,mul_add,
    zero_mul,add_zero] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFullFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full initial Fourier observation on an arbitrary positive window. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedFullObservation_normalized (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaShiftedFullObservation b h W a d hK s=
      cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma s)*
        cubicThetaShiftedFrequencyDirichlet b h s*cubicThetaShiftedWindowRadialTest h W a d s := by
  let f : ℂ×ℝ → ℂ := fun p => star (W p.2*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ))*
    (cubicThetaResidueScale*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s)
  have hc : Continuous (fun p : CubicThetaPoint => cubicThetaEisenstein p.val s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaEisenstein_continuousAt (by linarith) p.property).comp
      continuous_subtype_val.continuousAt
  have hcomp := hc.comp (continuous_const_smul (cubicThetaShiftedInversion b))
  have hf : Continuous (fun p : CubicThetaPoint =>
      star (cubicThetaShiftedFourierWeight h W p)*(cubicThetaResidueScale*
        cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s)) :=
    (cubicThetaShiftedFourierWeight_continuous h W).star.mul
    (continuous_const.mul hcomp)
  have hfc : Continuous (fun p : CubicThetaPoint => f (cubicThetaPointCoordinates p)) :=
    hf.congr (fun _ => rfl)
  have hi : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure :=
    (hfc.continuousOn.integrableOn_compact hK).mono_set hSK
  have hp : cubicThetaShiftedFullObservation b h W a d hK s=
      ∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure := by
    rw [cubicThetaShiftedFullObservation_right b h W a d hK hSK hs,←integral_const_mul]
    apply setIntegral_congr_fun (cubicThetaShiftedWindow_measurable a d)
    intro p _
    change cubicThetaResidueScale*(star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s)=_
    dsimp only [f,cubicThetaShiftedFourierWeight,cubicThetaPointCoordinates]
    rw [cubicThetaFullPointAction_apply]
    ring
  rw [hp,cubicThetaShiftedWindow_fubini ha d f hi,cubicThetaShiftedWindowRadialTest,
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  have hv0 : 0<v := ha.trans_le hv.1
  calc
    _ = cubicThetaResidueScale*star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaShiftedHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
            cubicThetaEisenstein ((cubicThetaInversion 1 (z,v)).1+b,
              (cubicThetaInversion 1 (z,v)).2) s := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaShiftedHorizontalCell_measurable
      intro z _
      simp only [f,cubicThetaMobius_shiftedInversion b (p:=(z,v)) hv0,star_mul]
      ring
    _ = _ := by rw [cubicThetaShifted_horizontal_coefficient b hv0 (by linarith) h]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPositiveConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing of the actual constant coefficient at every positive height
for the two nontrivial translated cusps. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedPositiveZero_observation_germ (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a : ℝ} (ha : 0<a) (d : ℝ)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK
      =ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hL : MeromorphicOn
      (cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK)
      {z : ℂ | 1<z.re} := fun z hz =>
    cubicThetaShiftedFullObservation_meromorphic _ 0 W ha d hK hz
  have hR : MeromorphicOn (fun _ : ℂ => (0:ℂ)) {z : ℂ | 1<z.re} :=
    fun z _ => MeromorphicAt.const 0 z
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hnear : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hnear] with z hz
  have hD : cubicThetaShiftedFrequencyDirichlet ((m:Eisenstein)+n*omegaE) 0 z=0 := by
    rw [cubicThetaShiftedFrequencyDirichlet_eq,zero_sub,←neg_mul,ite_eq_right hn]
  rw [cubicThetaShiftedFullObservation_normalized _ 0 W ha d hK hSK hz,hD,
    mul_zero,zero_mul]

lemma cubicThetaShiftedPositiveZero_window_pairing (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) :
    (∫ v in Icc a d,star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v/(v:ℂ)^3)=0 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  have hg := cubicThetaShiftedPositiveZero_observation_germ m n hn W (by linarith : 0<a) d hK hSK
    (s:=(4/3:ℂ)) (by norm_num)
  have ht : Tendsto (fun z : ℂ => (z-4/3)*
      cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK z)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hg] with z hz
    simp only [hz,mul_zero]
  rw [←cubicThetaShiftedModel_window_pairing _ 0 W (by linarith) d]
  exact tendsto_nhds_unique (cubicThetaShiftedFullObservation_residue _ 0 W ha d hK hSK) ht


theorem cubicThetaShiftedPositiveConstantCoefficient_zero (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein)) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 := by
  let F : ℝ → ℂ := fun t =>
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 t/(t:ℂ)^3
  have hF : ContinuousOn F (Ioi (0:ℝ)) := by
    have hnum := cubicThetaShiftedModelHorizontal_continuous ((m:Eisenstein)+n*omegaE) 0
    have hden : ContinuousOn (fun t : ℝ => (t:ℂ)^3) (Ioi (0:ℝ)) :=
      (Complex.continuous_ofReal.pow 3).continuousOn
    exact hnum.div hden (fun t ht => pow_ne_zero 3
      (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))
  have hz := cubicThetaPositiveHeightWindow_separates hF (fun W a d ha _ => by
    have he := cubicThetaShiftedPositiveZero_window_pairing m n hn W (d:=d) ha
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext t
    dsimp [F]
    ring) hv
  have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hv))
  exact (div_eq_iff hv0).mp hz |>.trans (zero_mul _)

theorem cubicThetaShiftedPositiveConstantCoefficient_nontrivial (m n : ℤ)
    (hn : ¬(3:ℤ) ∣ n) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 :=
  cubicThetaShiftedPositiveConstantCoefficient_zero m n
    (cubicThetaShifted_nontrivial_constant n hn) hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFullResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full corrected compact observations identify the actual translated
residue at every positive height, including the low-height incoming term. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaShiftedFullWindow_regularized_germ (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    {s : ℂ} (hs : 1 < s.re) :
    (fun z => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      =ᶠ[𝓝[≠] s]
    (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z) := by
  have hL : MeromorphicOn
      (fun z => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
      (cubicThetaShiftedFullObservation_meromorphic _ h W ha d hK hz)
  have hR : MeromorphicOn (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const cubicThetaResidueScale z).mul
      ((MeromorphicAt.const (Real.pi:ℂ) z).div
        (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt)).mul
      (cubicThetaRegularizedShiftedFrequency_analytic n hh z hz).meromorphicAt).mul
      ((cubicThetaShiftedWindowRadial_entire hh W ha had).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaShiftedFullObservation_normalized _ h W ha d hK hSK hz,
    cubicThetaRegularizedShiftedFrequency_right m n hh hz]
  ring

theorem cubicThetaShiftedFullWindow_residue_coefficient (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    :
    (∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex
          (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) p.val)
      ∂cubicThetaPointMeasure)=
    cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
      cubicThetaRegularizedShiftedFrequency n h (4/3)*
        cubicThetaShiftedWindowRadialTest h W a d (4/3) := by
  have hc : ContinuousAt (fun z => cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedShiftedFrequency n h z*cubicThetaShiftedWindowRadialTest h W a d z)
      (4/3:ℂ) :=
    ((continuousAt_const.mul (continuousAt_const.div
      (cubicThetaGamma_analytic_right (by norm_num : (0:ℝ)<(4/3:ℂ).re)).continuousAt
        (Complex.Gamma_ne_zero_of_re_pos (by norm_num)))).mul
      (cubicThetaRegularizedShiftedFrequency_analytic n hh (4/3) (by norm_num)).continuousAt).mul
      ((cubicThetaShiftedWindowRadial_entire hh W ha had).analyticAt (4/3)).continuousAt
  have ht : Tendsto
      (fun z : ℂ => (z-4/3)*cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) h W a d hK z)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
        cubicThetaRegularizedShiftedFrequency n h (4/3)*
          cubicThetaShiftedWindowRadialTest h W a d (4/3))) := by
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact (cubicThetaShiftedFullWindow_regularized_germ m n hh W ha had hK hSK
      (s:=(4/3:ℂ)) (by norm_num)).symm
  exact tendsto_nhds_unique
    (cubicThetaShiftedFullObservation_residue _ h W ha d hK hSK) ht


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPositivePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full residue pairings on every positive-height compact interval. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedPositiveResidue_window_eq (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3)=
    ∫ v in Icc a d,star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  rw [←cubicThetaShiftedModel_window_pairing _ h W (by linarith) d,
    cubicThetaShiftedFullWindow_residue_coefficient m n hh W (by linarith) had hK hSK]
  rw [cubicThetaShiftedWindowRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  unfold cubicThetaShiftedResidueFactor cubicThetaShiftedPoleRadial
  ring

lemma cubicThetaShiftedPositiveResidue_window_zero (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*
      ((cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v-
        cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3))=0 := by
  have hpos : ∀ v∈Icc a d,(v:ℂ)^3≠0 := fun v hv =>
    pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by have := hv.1; linarith))
  have hF : ContinuousOn (fun v => star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul
      ((cubicThetaShiftedModelHorizontal_continuous _ h).mono
        (fun _ hv => lt_of_lt_of_le ha hv.1))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have hG : ContinuousOn (fun v => star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul (continuousOn_const.mul
      ((cubicThetaShiftedPoleRadial_continuous hh).mono
        (fun _ hv => lt_of_lt_of_le ha hv.1)))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have he := cubicThetaShiftedPositiveResidue_window_eq m n hh W ha had
  rw [←sub_eq_zero,←integral_sub (hF.integrableOn_compact isCompact_Icc)
    (hG.integrableOn_compact isCompact_Icc)] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext v
  ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPositivePointwise
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise translated-cusp coefficients throughout the upper half-space. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedPositiveCoefficient_on_window (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {a d v : ℝ} (ha : 0<a) (hv : v∈Ioo a d) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v := by
  let J : ℝ → ℂ := fun t =>
    (cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h t-
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h t)/(t:ℂ)^3
  have hsub : Ioo a d⊆Ioi (0:ℝ) := fun t ht => by change 0<t; linarith [ht.1]
  have hJ : ContinuousOn J (Ioo a d) :=
    (((cubicThetaShiftedModelHorizontal_continuous _ h).mono hsub).sub
      (continuousOn_const.mul ((cubicThetaShiftedPoleRadial_continuous hh).mono hsub))).div
      (Complex.continuous_ofReal.pow 3).continuousOn
      (fun t ht => pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hsub ht))))
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ),t∈Ioo a d → J t=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hJ.locallyIntegrableOn measurableSet_Ioo)
    intro g hg hgc hgs
    let W : C_c(ℝ,ℂ) :=
      ⟨⟨fun t => (g t:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
        hgc.comp_left Complex.ofReal_zero⟩
    have hz := cubicThetaShiftedPositiveResidue_window_zero m n hh W ha (le_trans hv.1.le hv.2.le)
    have he : (∫ t : ℝ,g t • J t)=∫ t in Icc a d,g t • J t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g t=0 := image_eq_zero_of_notMem_tsupport
        (fun hs => ht ⟨(hgs hs).1.le,(hgs hs).2.le⟩)
      rw [hg0,zero_smul]
    rw [he]
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul,J] using hz
  have hzero' : J=ᵐ[volume.restrict (Ioo a d)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hzero] with t ht he
    exact he ht
  have he := Measure.eqOn_open_of_ae_eq hzero' isOpen_Ioo hJ continuousOn_const
  have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hsub hv)))
  have hval := (div_eq_iff hv0).mp (he hv)
  exact sub_eq_zero.mp (by simpa only [Pi.zero_apply,zero_mul] using hval)

theorem cubicThetaShiftedPositiveCoefficient_pointwise (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v := by
  apply cubicThetaShiftedPositiveCoefficient_on_window m n hh (a:=v/2) (d:=v+1)
  · linarith
  · constructor <;> linarith


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPositiveSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full translated-cusp expansions at every positive height. The incoming
correction has disappeared on taking the actual spectral residue. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedPositiveCoefficient_whittaker (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (cubicThetaShiftedResidueFactor n h*
        ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ))*
        cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v) := by
  rw [cubicThetaShiftedPositiveCoefficient_pointwise m n hh hv,cubicThetaShiftedPoleRadial,
    cubicThetaShiftedPoleHeat_whittaker hh hv]
  ring

lemma cubicThetaShiftedModelHorizontal_positive_term (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (h : Eisenstein) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaShiftedModelTerm n v h := by
  by_cases hh : h=0
  · subst h
    rw [cubicThetaShiftedPositiveConstantCoefficient_nontrivial m n hn hv]
    simp only [cubicThetaShiftedModelTerm,ite_true, if_true,smul_zero]
  · have hc : (((81*Real.sqrt 3/2:ℝ):ℂ))≠0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    rw [cubicThetaShiftedPositiveCoefficient_whittaker m n hh hv]
    simp only [cubicThetaShiftedModelTerm,ite_eq_right hh,
      cubicThetaShiftedNormalizedCoefficient,Complex.real_smul]
    field_simp

theorem cubicThetaShiftedPositiveSeriesIdentity (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaShiftedModelSeries n z v := by
  have hf := cubicThetaContinuousFourier_ext
    (cubicThetaShifted_actual_continuous ((m:Eisenstein)+n*omegaE) hv)
    (cubicThetaShiftedModelSeries_continuous n hv)
    (fun a w => cubicThetaShifted_actual_periodic _ a hv w)
    (fun a w => cubicThetaShiftedModelSeries_periodic n v a w) (fun h => by
      have he := (cubicThetaShiftedModelHorizontal_positive_term m n hn hv h).trans
        (cubicThetaShiftedModelSeries_coefficient n hv h).symm
      unfold cubicThetaShiftedModelHorizontal at he
      rw [cubicThetaShiftedCell_integral_scaled,cubicThetaShiftedCell_integral_scaled] at he
      simp only [cubicThetaShifted_phase_tripled,cubicThetaHorizontalCharacter,
        Complex.real_smul,Complex.ofReal_ofNat] at he
      exact mul_left_cancel₀ (by norm_num : (9:ℂ)≠0) he)
  have he := congrFun hf (z/3)
  simpa only [show 3*(z/3)=z by ring] using he

theorem cubicThetaShiftedPositiveSeries_common (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaArithmeticBaseScalar*
        cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) (z,v) := by
  rw [cubicThetaShiftedPositiveSeriesIdentity m n hn hv,cubicThetaShiftedModelSeries_common]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaInteger
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariance under the whole integer modular group, derived from its
proved S,T generation and the two explicit reciprocity calculations. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaIntegerEmbedding_S :
    cubicThetaIntegerEmbedding ModularGroup.S = cubicThetaModularS := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change ((ModularGroup.S i j:ℤ):Eisenstein) = cubicThetaModularS i j
  fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.S,cubicThetaModularS]

lemma cubicThetaIntegerEmbedding_T :
    cubicThetaIntegerEmbedding ModularGroup.T = cubicThetaModularT := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change ((ModularGroup.T i j:ℤ):Eisenstein) = cubicThetaModularT i j
  fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.T,cubicThetaModularT]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegerPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additional integer translation in the full theta group follows
from the proved arithmetic support and the elementary trace pairing. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFrequency_integer_phase_cube {n : Eisenstein} (hn : lambdaE^3 ∣ n) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1 := by
  obtain ⟨k,hk⟩ := hn
  have hf : cubicThetaFrequency n=(k:ℂ)/traceLambda := by
    rw [hk,cubicThetaFrequency]
    push_cast
    rw [lambdaE_coe]
    field_simp [traceLambda_ne_zero]
  have ht : tracePair (cubicThetaFrequency n) 1=tracePair (k:ℂ) (1/traceLambda) := by
    rw [hf]
    unfold tracePair
    congr 1
    apply congrArg Complex.re
    ring
  rw [ht,tracePhase_div_lambda_one]

lemma cubicThetaFrequency_integer_phase_primary {h : Eisenstein} (hh : primary h) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (lambdaE*h)) 1):ℂ)=1 := by
  have hp := cubicThetaNinePhase_three_integer_primary hh (-1)
  rw [cubicThetaNinePhase,residueFourierChar_mk] at hp
  have hlam : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun x : Eisenstein => (x:ℂ)) lambdaE_sq
    push_cast at he
    rwa [lambdaE_coe] at he
  have ht : tracePair (cubicThetaFrequency (lambdaE*h)) 1=
      tracePair (((-1:ℤ):Eisenstein)*3*h:ℂ) (1/(((9:Eisenstein):ℂ)*traceLambda)) := by
    unfold tracePair
    congr 1
    apply congrArg Complex.re
    rw [cubicThetaFrequency_div_nine]
    push_cast
    rw [lambdaE_coe]
    rw [show ((9:Eisenstein):ℂ)=(9:ℂ) from rfl]
    field_simp [traceLambda_ne_zero]
    linear_combination (h:ℂ)*hlam
  rw [ht]
  exact hp

lemma cubicThetaFrequency_integer_phase_neg {n : Eisenstein}
    (hn : (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (-n)) 1):ℂ)=1 := by
  have ht : tracePair (cubicThetaFrequency (-n)) 1= -tracePair (cubicThetaFrequency n) 1 := by
    simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div,tracePair,mul_one,Complex.neg_re]
    ring
  rw [ht,AddChar.map_neg_eq_inv,Circle.coe_inv,hn,inv_one]

lemma cubicThetaArithmeticCoefficient_integer_phase {n : Eisenstein}
    (hn : cubicThetaArithmeticCoefficient n≠0) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1 := by
  have hR : Nonempty (CubicThetaCoordinates n) := by
    by_contra h
    exact hn (by simp only [cubicThetaArithmeticCoefficient,dite_eq_right h])
  let R := Classical.choice hR
  have hcoeff : R.coefficient≠0 := by
    rwa [←cubicThetaArithmeticCoefficient_formula R]
  have hcases : 3≤R.order ∨ R.order=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)= -1) := by
    unfold CubicThetaCoordinates.coefficient at hcoeff
    split_ifs at hcoeff with h0 h1
    · exact Or.inl h0.2
    · by_cases ho : 3≤R.order
      · exact Or.inl ho
      · exact Or.inr ⟨by omega,h1.2⟩
    · exact False.elim (hcoeff rfl)
  rcases hcases with ho | ⟨ho,hu⟩
  · apply cubicThetaFrequency_integer_phase_cube
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ho
    refine ⟨(R.unit:Eisenstein)*lambdaE^k*(R.squarefreePart*R.cubePart^3),?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,pow_add]; ring
  · have hp : primary (R.squarefreePart*R.cubePart^3) :=
      primary_mul R.squarefree_primary (by
        simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
          primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
    rw [R.numerator_eq,ho,pow_one]
    rcases hu with hu | hu
    · rw [hu,one_mul]
      exact cubicThetaFrequency_integer_phase_primary hp
    · rw [hu,neg_one_mul,neg_mul]
      exact cubicThetaFrequency_integer_phase_neg (cubicThetaFrequency_integer_phase_primary hp)

lemma cubicThetaArithmeticTerm_integer_periodic (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient (z+1) v n=
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  by_cases ha : cubicThetaArithmeticCoefficient n=0
  · simp [cubicThetaSeriesTerm,ha]
  have ht : tracePair (cubicThetaFrequency n) (z+1)=
      tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) 1 := by
    unfold tracePair
    simp only [mul_add,Complex.add_re,mul_add]
  simp only [cubicThetaSeriesTerm,ite_eq_right hn]
  rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul,
    cubicThetaArithmeticCoefficient_integer_phase ha,mul_one]

theorem cubicThetaArithmetic_integer_periodic (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (z+1,v)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  unfold cubicThetaNonconstant
  exact tsum_congr (fun n => cubicThetaArithmeticTerm_integer_periodic n z v)

theorem cubicThetaNormalizedSeries_integer_periodic {z : ℂ} {v : ℝ} (hv : 0<v) :
    cubicThetaNormalizedSeriesSection.val (⟨(z+1,v),hv⟩ : CubicThetaPoint)=
      cubicThetaNormalizedSeriesSection.val (⟨(z,v),hv⟩ : CubicThetaPoint) := by
  calc
    _ = cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (z+1,v) :=
      cubicThetaNormalizedSeriesSection_apply (⟨(z+1,v),hv⟩ : CubicThetaPoint)
    _ = cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) :=
      congrArg (fun w => cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+w)
        (cubicThetaArithmetic_integer_periodic z v)
    _ = _ := (cubicThetaNormalizedSeriesSection_apply (⟨(z,v),hv⟩ : CubicThetaPoint)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExtendedAutomorphy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reconstructed arithmetic theta section has the actual Gamma_2
multiplier. Its integer invariance follows from S,T generation. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaNormalizedSeries_modularT (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaModularT • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have hm : cubicThetaModularT=cubicThetaFullTranslation 1 := by
    apply Subtype.ext
    rfl
  have hp : (cubicThetaModularT • p).val=(p.val.1+1,p.val.2) := by
    rw [hm,cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,
      cubicThetaMobius_translation]
    simp only [Subalgebra.coe_one]
  have hpoint : cubicThetaModularT • p=(⟨(p.val.1+1,p.val.2),p.property⟩ : CubicThetaPoint) :=
    Subtype.ext hp
  rw [hpoint]
  exact cubicThetaNormalizedSeries_integer_periodic p.property

theorem cubicThetaNormalizedSeries_integer (u : SL(2,ℤ)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding u • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have hgen : Subgroup.closure {ModularGroup.S,ModularGroup.T} ≤
      cubicThetaNormalizedStabilizer.comap cubicThetaIntegerEmbedding := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · change ∀ p : CubicThetaPoint,
        cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding ModularGroup.S • p)=_
      rw [cubicThetaIntegerEmbedding_S]
      exact cubicThetaNormalizedSeriesSection_inversion
    · have haT := Set.mem_singleton_iff.mp ha
      subst a
      change ∀ p : CubicThetaPoint,
        cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding ModularGroup.T • p)=_
      rw [cubicThetaIntegerEmbedding_T]
      exact cubicThetaNormalizedSeries_modularT
  have hu : u∈Subgroup.closure {ModularGroup.S,ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  exact hgen hu p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryBottom
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full integral matrix with primary lower-left entry reduces to an
actual translated inversion through a principal-level matrix. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaNormalizedSeries_primaryBottom (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaNormalizedSeriesSection.val
          (cubicThetaShiftedInversion (g 0 0) • (cubicThetaFullTranslation (g 1 1) • p)) := by
  have hg : g=(cubicThetaPrimaryBottomPrincipal g hc).val*cubicThetaPrimaryBottomSeed g := by
    change g=(g*(cubicThetaPrimaryBottomSeed g)⁻¹)*cubicThetaPrimaryBottomSeed g
    simp
  calc
    _ = cubicThetaNormalizedSeriesSection.val
        (cubicThetaPrimaryBottomPrincipal g hc • (cubicThetaPrimaryBottomSeed g • p)) := by
      change cubicThetaNormalizedSeriesSection.val (g • p)=
        cubicThetaNormalizedSeriesSection.val
          ((cubicThetaPrimaryBottomPrincipal g hc).val • (cubicThetaPrimaryBottomSeed g • p))
      rw [←mul_smul]
      exact congrArg (fun u : SL(2,Eisenstein) => cubicThetaNormalizedSeriesSection.val (u • p)) hg
    _ = cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaNormalizedSeriesSection.val (cubicThetaPrimaryBottomSeed g • p) :=
      cubicThetaNormalizedSeriesSection.property _ _
    _ = _ := by rw [cubicThetaPrimaryBottomSeed,mul_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspTypes
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three translated inversion types needed for primary bottom rows.
The actual constant is retained at the trivial type. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullTranslation_add (a b : Eisenstein) :
    cubicThetaFullTranslation (a+b)=cubicThetaFullTranslation a*cubicThetaFullTranslation b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,a;0,1]*!![1,b;0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaShiftedInversion_factor (b : Eisenstein) :
    cubicThetaShiftedInversion b=cubicThetaFullTranslation b*cubicThetaFullInversion := by
  apply Subtype.ext
  change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaNormalizedSeries_integer_translation (m : ℤ) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (m:Eisenstein) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  let u : SL(2,ℤ) := ⟨!![1,m;0,1],by simp [Matrix.det_fin_two]⟩
  have he : cubicThetaIntegerEmbedding u=cubicThetaFullTranslation (m:Eisenstein) := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change ((u i j:ℤ):Eisenstein)=(cubicThetaFullTranslation (m:Eisenstein)) i j
    fin_cases i <;> fin_cases j <;> norm_num [u,cubicThetaFullTranslation]
  rw [←he]
  exact cubicThetaNormalizedSeries_integer u p

lemma cubicThetaNormalizedSeries_triple_translation (b : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (3*b) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have he : cubicThetaFullTranslation (3*b)=(cubicThetaPrincipalTranslation b).val := rfl
  rw [he]
  change cubicThetaNormalizedSeriesSection.val (cubicThetaPrincipalTranslation b • p)=_
  rw [cubicThetaNormalizedSeriesSection.property,cubicThetaPrincipalTranslation_value,one_mul]

lemma cubicThetaNormalizedSeries_shifted_trivial (m n : ℤ) (hn : (3:ℤ) ∣ n)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  obtain ⟨t,rfl⟩ := hn
  have he : (m:Eisenstein)+((3*t:ℤ):Eisenstein)*omegaE=
      (m:Eisenstein)+3*((t:Eisenstein)*omegaE) := by push_cast; ring
  rw [he,cubicThetaShiftedInversion_factor,cubicThetaFullTranslation_add,mul_smul,mul_smul,
    cubicThetaNormalizedSeries_integer_translation,cubicThetaNormalizedSeries_triple_translation,
    cubicThetaNormalizedSeriesSection_inversion]

lemma cubicThetaNormalizedSeries_shifted_nontrivial (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) p.val)=_
  rw [cubicThetaShiftedPositiveSeries_common m n hn p.property p.val.1,←mul_assoc,
    inv_mul_cancel₀ cubicThetaArithmeticBaseScalar_ne_zero,one_mul]

theorem cubicThetaNormalizedSeries_shifted_complete (m n : ℤ) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaCuspExpansion n p.val := by
  by_cases hn : (3:ℤ) ∣ n
  · rw [cubicThetaNormalizedSeries_shifted_trivial m n hn p,cubicThetaCuspExpansion,ite_eq_left hn]
    exact cubicThetaNormalizedSeriesSection_apply p
  · rw [cubicThetaNormalizedSeries_shifted_nontrivial m n hn p,cubicThetaCuspExpansion,ite_eq_right hn]

theorem cubicThetaNormalizedSeries_primaryBottom_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (m n : ℤ) (ha : g 0 0=(m:Eisenstein)+n*omegaE)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaCuspExpansion n (cubicThetaFullTranslation (g 1 1) • p).val := by
  rw [cubicThetaNormalizedSeries_primaryBottom g hc p,ha,
    cubicThetaNormalizedSeries_shifted_complete]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary projector and its finite transformed cusp family. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaCuspCoordinates (b : Eisenstein) :
    b=((coordinatesEquiv.symm b 0:ℤ):Eisenstein)+cubicThetaCuspIndex b*omegaE :=
  (coordinatesEquiv.apply_symm_apply b).symm

lemma cubicThetaNormalizedSeries_primaryBottom_index (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaCuspExpansion (cubicThetaCuspIndex (g 0 0))
          (cubicThetaFullTranslation (g 1 1) • p).val :=
  cubicThetaNormalizedSeries_primaryBottom_complete g hc
    (coordinatesEquiv.symm (g 0 0) 0) (cubicThetaCuspIndex (g 0 0))
    (cubicThetaCuspCoordinates (g 0 0)) p

lemma cubicThetaProjectedCusp_identity_oai (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (j : Fin 3) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))=
      cubicThetaProjectedCuspMultiplier g hc j*
        cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
          (cubicThetaFullTranslation (g 1 1) • p).val := by
  rw [←mul_smul]
  have he := cubicThetaNormalizedSeries_primaryBottom_index (cubicThetaProjectedCuspMatrix g j)
    (cubicThetaProjectedCuspMatrix_primary g hc j) p
  rw [show cubicThetaProjectedCuspMatrix g j 1 1=g 1 1 from
    (cubicThetaFullTranslation_mul_bottom _ g).2] at he
  exact he

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity_oai := @OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity_oai
